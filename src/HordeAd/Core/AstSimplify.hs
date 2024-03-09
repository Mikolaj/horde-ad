{-# LANGUAGE AllowAmbiguousTypes, TupleSections #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
-- | Term-simplifying combinators corresponding to the Ast constructors
-- and complete bottom-up simplifying functions. The former
-- simplify only on the basis of inspecting the roots of their
-- argument term trees. If the arguments get modified as a result,
-- the modified forms are again inspected and may be simplified.
-- The latter traverse and simplify the whole term.
--
-- The limited simplification via combinators is enough to uncover redexes
-- for the vectorization rules to fire and to undo some of the complication
-- introduced by vectorization. The intention is to leave as much
-- of the original terms provided by the user as possible while making
-- sure subterms introduced by vectorization are maximally simplified.
module HordeAd.Core.AstSimplify
  ( -- * Permutation operations
    simplifyPermutation
    -- * The combinators for indexing and gather
  , simplifyStepNonIndex, simplifyStepNonIndexS, astIndexStep, astIndexStepS
  , astGatherStep, astGatherStepS
    -- * The simplifying combinators, one for most AST constructors
  , astLet, astLetS, astCond, astCondS, astSumOfList, astSumOfListS
  , astSum, astSumS, astScatter, astScatterS
  , astFromList, astFromListS, astFromVector, astFromVectorS
  , astReplicate, astReplicateS, astAppend, astAppendS, astSlice, astSliceS
  , astReverse, astReverseS
  , astTranspose, astTransposeS, astReshape, astReshapeS
  , astCast, astCastS, astFromIntegral, astFromIntegralS, astRFromS, astSFromR
  , astPrimalPart, astPrimalPartS, astDualPart, astDualPartS
  , astLetHVectorIn, astLetHVectorInS, astLetHFunIn, astLetHFunInS, astHApply
  , astLetHVectorInHVector, astLetHFunInHVector
  , astLetInHVector, astLetInHVectorS
    -- * The simplifying bottom-up pass
  , simplifyAst, simplifyAstHVector, simplifyAstS
    -- * Substitution payload and adaptors for AstVarName
  , SubstitutionPayload(..)
  , substituteAst, substitute1Ast, substituteAstIndex
  , substituteAstS, substitute1AstS, substituteAstIndexS
  , substituteAstHVector, substitute1AstHVector

    -- * Misc
  , astReplicate0N
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (mapAndUnzipM)
import qualified Data.Array.Convert
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Int (Int64)
import           Data.Kind (Type)
import           Data.List (dropWhileEnd)
import           Data.Maybe (catMaybes, fromMaybe, isJust, isNothing)
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
  , AstHVector
  , AstRanked (AstConst, AstN1, AstN2, AstSumOfList)
  , AstShaped (AstConstS, AstN1S, AstN2S, AstSumOfListS)
  )
import           HordeAd.Core.Ast hiding
  (AstBool (..), AstHVector (..), AstRanked (..), AstShaped (..))
import qualified HordeAd.Core.Ast as Ast
import           HordeAd.Core.AstFreshId
import           HordeAd.Core.AstTools
import           HordeAd.Core.HVector
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.BackendConcrete
import           HordeAd.Internal.OrthotopeOrphanInstances
  (MapSucc, matchingRank, sameShape, trustMeThisIsAPermutation)
import           HordeAd.Util.ShapedList (ShapedList (..))
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex
import           HordeAd.Util.SizedList

-- * Expressing operations as Gather; introduces new variable names

-- We keep AstTranspose terms for as long as possible, because
-- they are small and fuse nicely in many cases. For some forms of indexing
-- and nesting with reshape and gather they don't fuse, which is when
-- this function is invoked.
astTransposeAsGather
  :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
  => Permutation -> AstRanked s r n -> AstRanked s r n
{-# NOINLINE astTransposeAsGather #-}
astTransposeAsGather perm v =
  let pInt = length perm
  in case someNatVal $ toInteger pInt of
    Just (SomeNat @p _) -> do
      funToVarsIx pInt $ \ (!vars, !ix) ->
        let asts :: AstIndex p
            asts = permutePrefixIndex perm ix
        in case cmpNat (Proxy @p) (Proxy @n) of
          EQI -> astGatherR @p @(n - p)
                            (backpermutePrefixShape perm (shapeAst v)) v
                            (vars, asts)
          LTI -> astGatherR @p @(n - p)
                            (backpermutePrefixShape perm (shapeAst v)) v
                            (vars, asts)
          _ -> error "astTransposeAsGather: permutation longer than rank"
    Nothing -> error "astTransposeAsGather: impossible someNatVal error"

astTransposeAsGatherS
  :: forall perm sh s r p.
     (Sh.Shape perm, Sh.Shape sh, Sh.Rank perm <= Sh.Rank sh, p ~ Sh.Rank perm)
  => AstShaped s r sh -> AstShaped s r (Sh.Permute perm sh)
{-# NOINLINE astTransposeAsGatherS #-}
astTransposeAsGatherS v =
  Sh.withShapeP (drop (length (Sh.shapeT @perm))
                 $ Sh.shapeT @sh) $ \(Proxy @shd) ->
    gcastWith (unsafeCoerce Refl :: Sh.Drop p sh :~: shd) $
    Sh.withShapeP (take (length (Sh.shapeT @perm))
                   $ Sh.shapeT @sh) $ \(Proxy @shp) ->
      gcastWith (unsafeCoerce Refl :: Sh.Take p sh :~: shp) $
      Sh.withShapeP (backpermutePrefixList (Sh.shapeT @perm)
                                           (Sh.shapeT @shp)) $ \(Proxy @sh2) ->
        gcastWith (unsafeCoerce Refl
                   :: Sh.Permute perm (Sh.Take p sh) :~: sh2) $
        funToVarsIxS @sh2 $ \ (!vars, !ix) ->
          let asts :: AstIndexS (Sh.Take p sh)
              asts = ShapedList.permutePrefixSized (Sh.shapeT @perm) ix
          in gcastWith (unsafeCoerce Refl
                        :: Sh.Permute perm sh :~: sh2 Sh.++ Sh.Drop p sh) $
             astGatherS @sh2 @p @sh v (vars, asts)

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
  :: forall p m s r. (KnownNat p, KnownNat m, GoodScalar r, AstSpan s)
  => ShapeInt m -> AstRanked s r p -> AstRanked s r m
{-# NOINLINE astReshapeAsGather #-}
astReshapeAsGather shOut v =
  funToVarsIx (lengthShape shOut) $ \ (!vars, !ix) ->
    let shIn = shapeAst v
        asts :: AstIndex p
        asts = let i = toLinearIdx @m @0 shOut ix
               in simplifyAst <$> fromLinearIdx shIn i
                    -- we generate these, so we simplify
    in astGatherR @m @0 shOut v (vars, asts)

astReshapeAsGatherS
  :: forall sh sh2 r s. (Sh.Shape sh, Sh.Shape sh2, Sh.Size sh ~ Sh.Size sh2)
  => AstShaped s r sh -> AstShaped s r sh2
{-# NOINLINE astReshapeAsGatherS #-}
astReshapeAsGatherS v =
  gcastWith (unsafeCoerce Refl :: sh2 Sh.++ '[] :~: sh2) $
  funToVarsIxS @sh2 $ \ (!vars, !ix) ->
    let shIn = ShapedList.shapeSh @sh
        shOut = ShapedList.shapeSh @sh2
        asts :: AstIndexS sh
        asts = let i :: ShapedList.ShapedNat (Sh.Size sh2) AstInt
                   i = ShapedList.toLinearIdx @sh2 @'[] shOut ix
               in simplifyAst <$> ShapedList.fromLinearIdx shIn i
                    -- we generate these, so we simplify
    in gcastWith (unsafeCoerce Refl :: Sh.Take (Sh.Rank sh) sh :~: sh) $
       gcastWith (unsafeCoerce Refl :: Sh.Drop (Sh.Rank sh) sh :~: '[]) $
       astGatherS @sh2 @(Sh.Rank sh) @sh v (vars, asts)


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


-- * The combinators for indexing and gather

-- This does a single step of simplification of any non-indexing term
-- (many steps if guaranteed net beneficial). Terms representing integers
-- and and AstBool terms are simplified as much as possible.
simplifyStepNonIndex
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => AstRanked s r n -> AstRanked s r n
simplifyStepNonIndex t = case t of
  Ast.AstVar{} -> t
  Ast.AstLet var u v -> astLet var u v
  Ast.AstLetADShare{} -> error "simplifyStepNonIndex: AstLetADShare"
  Ast.AstCond a b c -> astCond a b c
  Ast.AstMinIndex{} -> t
  Ast.AstMaxIndex{} -> t
  Ast.AstFloor{} -> t
  Ast.AstIota -> t
  AstN1 opCode u ->
    case isRankedInt u of
      Just Refl -> simplifyAstNumOp1 opCode u
      _ -> t
  AstN2 opCode u v ->
    case isRankedInt u of
      Just Refl -> simplifyAstNumOp2 opCode u v
      _ -> t
  Ast.AstR1{} -> t
  Ast.AstR2{} -> t
  Ast.AstI2 opCode u v ->
    case isRankedInt u of
      Just Refl -> simplifyAstIntegralOp2 opCode u v
      _ -> t
  AstSumOfList args ->
    case isRankedInt t of
      Just Refl -> foldr1 simplifyAstPlusOp args
      _ -> t
  Ast.AstIndex{} -> t  -- was supposed to be *non*-index
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
  Ast.AstGather _ v0 (ZR, ix) -> Ast.AstIndex v0 ix
  Ast.AstGather sh v0 (_, ZIR) -> astReplicateN sh v0
  Ast.AstGather{} -> t  -- this is "index" enough
  Ast.AstCast v -> astCast v
  Ast.AstFromIntegral v -> astFromIntegral v
  AstConst{} -> t
  Ast.AstLetHVectorIn vars u v -> astLetHVectorIn vars u v
  Ast.AstLetHFunIn var u v -> astLetHFunIn var u v
  Ast.AstRFromS v -> astRFromS v
  Ast.AstConstant{} -> t
  Ast.AstPrimalPart v -> astPrimalPart v  -- has to be done sooner or later
  Ast.AstDualPart v -> astDualPart v
  Ast.AstD{} -> t

simplifyStepNonIndexS
  :: (Sh.Shape sh, GoodScalar r, AstSpan s)
  => AstShaped s r sh -> AstShaped s r sh
simplifyStepNonIndexS t = case t of
  Ast.AstVarS{} -> t
  Ast.AstLetS var u v -> astLetS var u v
  Ast.AstLetADShareS{} -> error "simplifyStepNonIndexS: AstLetADShareS"
  Ast.AstCondS a b c -> astCondS a b c
  Ast.AstMinIndexS{} -> t
  Ast.AstMaxIndexS{} -> t
  Ast.AstFloorS{} -> t
  Ast.AstIotaS -> t
  AstN1S{} -> t
  AstN2S{} -> t
  Ast.AstR1S{} -> t
  Ast.AstR2S{} -> t
  Ast.AstI2S{} -> t
  AstSumOfListS l -> astSumOfListS l
  Ast.AstIndexS{} -> t  -- was supposed to be *non*-index
  Ast.AstSumS v -> astSumS v
  Ast.AstScatterS v (vars, ix) -> astScatterS v (vars, ix)
  Ast.AstFromListS l -> astFromListS l
  Ast.AstFromVectorS l -> astFromVectorS l
  Ast.AstReplicateS v -> astReplicateS v
  Ast.AstAppendS x y -> astAppendS x y
  Ast.AstSliceS @i @k v -> astSliceS @i @k v
  Ast.AstReverseS v -> astReverseS v
  Ast.AstTransposeS @perm v -> astTransposeS @perm v
  Ast.AstReshapeS v -> astReshapeS v
  Ast.AstBuild1S{} -> t
  Ast.AstGatherS @_ @p @sh1 v0 (ZS, ix) ->
    gcastWith (unsafeCoerce Refl :: sh1 :~: Sh.Take p sh1 Sh.++ Sh.Drop p sh1)
    $ Ast.AstIndexS v0 ix
  Ast.AstGatherS @sh2 @p @sh1 v0 (_ , ZS) ->
    gcastWith (unsafeCoerce Refl :: Sh.Drop p sh1 :~: sh1) $
    astReplicateNS @sh2 @sh1 v0
  Ast.AstGatherS{} -> t  -- this is "index" enough
  Ast.AstCastS v -> astCastS v
  Ast.AstFromIntegralS v -> astFromIntegralS v
  AstConstS{} -> t
  Ast.AstLetHVectorInS vars u v -> astLetHVectorInS vars u v
  Ast.AstLetHFunInS var u v -> astLetHFunInS var u v
  Ast.AstSFromR v -> astSFromR v
  Ast.AstConstantS{} -> t
  Ast.AstPrimalPartS v -> astPrimalPartS v  -- has to be done sooner or later
  Ast.AstDualPartS v -> astDualPartS v
  Ast.AstDS{} -> t

astIndexR
  :: forall m n s r.
     (KnownNat m, KnownNat n, GoodScalar r, AstSpan s)
  => AstRanked s r (m + n) -> AstIndex m -> AstRanked s r n
astIndexR = astIndexROrStepOnly False

astIndexStep
  :: forall m n s r.
     (KnownNat m, KnownNat n, GoodScalar r, AstSpan s)
  => AstRanked s r (m + n) -> AstIndex m -> AstRanked s r n
astIndexStep v ix = astIndexROrStepOnly True (simplifyStepNonIndex v)
                                             (fmap simplifyAst ix)

astIndexS
  :: forall sh1 sh2 s r.
     ( Sh.Shape sh1, Sh.Shape sh2, Sh.Shape (sh1 Sh.++ sh2)
     , GoodScalar r, AstSpan s )
  => AstShaped s r (sh1 Sh.++ sh2) -> AstIndexS sh1
  -> AstShaped s r sh2
astIndexS = astIndexSOrStepOnly False

astIndexStepS
  :: forall sh1 sh2 s r.
     ( Sh.Shape sh1, Sh.Shape sh2, Sh.Shape (sh1 Sh.++ sh2)
     , GoodScalar r, AstSpan s )
  => AstShaped s r (sh1 Sh.++ sh2) -> AstIndexS sh1
  -> AstShaped s r sh2
astIndexStepS v ix = astIndexSOrStepOnly True (simplifyStepNonIndexS v)
                                              (fmap simplifyAst ix)

-- If stepOnly is set, we reduce only as long as needed to reveal
-- a non-indexing constructor or one of the normal forms (one-element
-- indexing applied to AstFromList or AstFromVector or indexing
-- of a term with no possible occurrences of Int variables). Otherwise,
-- we simplify exhaustively.
--
-- The v0 term is already at least one step simplified,
-- either from full recursive simplification or from astIndexStep.
astIndexROrStepOnly
  :: forall m n s r.
     (KnownNat m, KnownNat n, GoodScalar r, AstSpan s)
  => Bool -> AstRanked s r (m + n) -> AstIndex m -> AstRanked s r n
astIndexROrStepOnly stepOnly (Ast.AstIndex v ix) ZIR =
  astIndexROrStepOnly stepOnly v ix  -- no non-indexing constructor yet revealed
astIndexROrStepOnly _ v0 ZIR = v0
astIndexROrStepOnly stepOnly v0 ix@(i1 :.: (rest1 :: AstIndex m1)) =
 let astIndexRec, astIndex
       :: forall m' n' s'. (KnownNat m', KnownNat n', AstSpan s')
       => AstRanked s' r (m' + n') -> AstIndex m' -> AstRanked s' r n'
     astIndexRec vRec ZIR = vRec
     astIndexRec vRec ixRec =
       if stepOnly then Ast.AstIndex vRec ixRec else astIndexR vRec ixRec
     astIndex = if stepOnly then astIndexStep else astIndexR
     astGather
       :: forall m' n' p'.
          (KnownNat m', KnownNat p', KnownNat n')
       => ShapeInt (m' + n') -> AstRanked s r (p' + n')
       -> (AstVarList m', AstIndex p')
       -> AstRanked s r (m' + n')
     astGather = if stepOnly then astGatherStep else astGatherR
 in case v0 of
  Ast.AstVar{} -> Ast.AstIndex v0 ix
  Ast.AstLet var u v -> astLet var u (astIndexRec v ix)
  Ast.AstLetADShare{} -> error "astIndexROrStepOnly: AstLetADShare"
  Ast.AstCond b v w ->
    shareIx ix $ \ix2 -> astCond b (astIndexRec v ix2) (astIndexRec w ix2)
  Ast.AstMinIndex v -> Ast.AstMinIndex $ astIndexROrStepOnly stepOnly v ix
  Ast.AstMaxIndex v -> Ast.AstMaxIndex $ astIndexROrStepOnly stepOnly v ix
  Ast.AstFloor v -> Ast.AstFloor $ astIndexROrStepOnly stepOnly v ix
  Ast.AstIota | AstConst i <- i1 -> fromIntegral i
  Ast.AstIota -> Ast.AstIndex v0 ix
  AstN1 opCode u ->
    shareIx ix $ \ix2 -> AstN1 opCode (astIndexRec u ix2)
  AstN2 opCode u v ->
    shareIx ix $ \ix2 -> AstN2 opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstR1 opCode u ->
    shareIx ix
    $ \ix2 -> Ast.AstR1 opCode (astIndexRec u ix2)
  Ast.AstR2 opCode u v ->
    shareIx ix
    $ \ix2 -> Ast.AstR2 opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstI2 opCode u v ->
    shareIx ix
    $ \ix2 -> Ast.AstI2 opCode (astIndexRec u ix2) (astIndexRec v ix2)
  AstSumOfList args ->
    shareIx ix $ \ix2 -> astSumOfList (map (`astIndexRec` ix2) args)
  Ast.AstIndex v ix2 ->
    astIndex v (appendIndex ix2 ix)
  Ast.AstSum v ->  -- almost neutral; transposition is likely to fuse away
    let perm3 = backpermCycle $ valueOf @m + 1
    in astSum $ astIndex (astTranspose perm3 v) ix
  Ast.AstScatter @_ @n7 (_ :$: sh)
                 v (vars, AstIntVar var5 :.: (ix2 :: AstIndex p71))
    | AstIntVar var6 <- i1, var6 == var5 ->
        gcastWith (unsafeCoerce Refl :: m1 + n :~: p71 + n7) $
        astIndex (astScatter sh v (vars, ix2)) rest1
  Ast.AstScatter @_ @n7 (_ :$: sh)
                 v (vars, AstConst i5 :.: (ix2 :: AstIndex p71))
    | AstConst i6 <- i1 ->
        gcastWith (unsafeCoerce Refl :: m1 + n :~: p71 + n7) $
        if i6 == i5
        then astIndex (astScatter sh v (vars, ix2)) rest1
        else astIndex (astReplicate0N @(m1 + n) sh 0) rest1
  -- AstScatter sh v (vars2, ZIR) ->
  --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZIR)
  Ast.AstScatter{} ->  -- normal form
    Ast.AstIndex v0 ix
  Ast.AstFromList l | AstConst it <- i1 ->
    let i = fromIntegral $ OR.unScalar it
    in astIndex (if 0 <= i && i < length l
                 then l !! i
                 else astReplicate0N @(m1 + n)
                                     (dropShape $ shapeAst v0) 0) rest1
  Ast.AstFromList{} | ZIR <- rest1 ->  -- normal form
    Ast.AstIndex v0 ix
  Ast.AstFromList l ->
    shareIx rest1 $ \ix2 ->
      Ast.AstIndex (astFromList $ map (`astIndexRec` ix2) l)
                   (singletonIndex i1)
  Ast.AstFromVector l | AstConst it <- i1 ->
    let i = fromIntegral $ OR.unScalar it
    in astIndex (if 0 <= i && i < V.length l
                 then l V.! i
                 else astReplicate0N @(m1 + n)
                                     (dropShape $ shapeAst v0) 0) rest1
  Ast.AstFromVector{} | ZIR <- rest1 ->  -- normal form
    Ast.AstIndex v0 ix
  Ast.AstFromVector l ->
    shareIx rest1 $ \ix2 ->
      Ast.AstIndex (astFromVector $ V.map (`astIndexRec` ix2) l)
                   (singletonIndex i1)
  Ast.AstReplicate _k v ->
    astIndex v rest1
  Ast.AstAppend u v | AstConst it <- i1 ->
    let i = fromIntegral $ OR.unScalar it
        len = lengthAst u
    in if len > i
       then astIndex u ix
       else astIndex v (simplifyAst (i1 - fromIntegral len) :.: rest1)
  Ast.AstAppend{} ->  -- normal form
    {- We can't do the following, because we can get, e.g., division
       by zero in the index in the counterfactual branch and sometimes
       all branches are materialized. Similarly for gather of append
       and see the TODO there. Maybe this is fixable with gather working
       over a tensor product or something else that indexes in complex ways?
    let vlen = AstConst $ lengthAst v
        ix2 = simplifyAst (AstIntOp MinusIntOp [i1, vlen]) :.: rest1
    in case simplifyAstBool $ AstRelInt LsOp [i1, vlen] of
      AstBoolConst b -> if b then astIndex v ix else astIndex w ix2
      bExpr -> astCond bExpr (astIndexRec v ix) (astIndexRec w ix2)
    -}
    Ast.AstIndex v0 ix
  Ast.AstSlice i _k v ->
    let ii = simplifyAst (i1 + fromIntegral i)
      -- we generate this index, so we simplify on the spot
    in astIndex v (ii :.: rest1)
  Ast.AstReverse v ->
    let iRev = simplifyAst (fromIntegral (lengthAst v - 1) - i1)
      -- we generate this index, so we simplify on the spot
    in astIndex v (iRev :.: rest1)
  Ast.AstTranspose perm v | valueOf @m >= length perm ->
    astIndex v (permutePrefixIndex perm ix)
  Ast.AstTranspose perm v ->
    astIndex (astTransposeAsGather perm v) ix
  Ast.AstReshape sh v ->
    astIndex (astReshapeAsGather sh v) ix
  Ast.AstBuild1 _n2 (var2, v) ->
    astIndex (astLet var2 i1 v) rest1
  Ast.AstGather _sh v (ZR, ix2) -> astIndex v (appendIndex ix2 ix)
  Ast.AstGather @_ @n7 (_ :$: sh') v (var2 ::: (vars :: AstVarList m71), ix2) ->
    let w :: AstRanked s r (m1 + n)
        w = gcastWith (unsafeCoerce Refl :: m1 + n :~: m71 + n7) $
            astGather sh' v (vars, ix2)
    in astLet var2 i1 $ astIndex w rest1
  Ast.AstGather{} ->
    error "astIndex: AstGather: impossible pattern needlessly required"
  Ast.AstCast t -> astCast $ astIndexROrStepOnly stepOnly t ix
  Ast.AstFromIntegral v -> astFromIntegral $ astIndexROrStepOnly stepOnly v ix
  AstConst t ->
    let unConst :: AstRanked PrimalSpan Int64 0 -> Maybe [OR.Array 0 Int64]
                -> Maybe [OR.Array 0 Int64]
        unConst (AstConst i) (Just l) = Just $ i : l
        unConst _ _ = Nothing
    in case foldr unConst (Just []) ix of
      Just ixInt -> AstConst $ tindexZR t $ listToIndex
                    $ map OR.unScalar ixInt
        -- TODO: we'd need mapM for Index to keep this rank-typed
      Nothing -> Ast.AstIndex v0 ix
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars l (astIndexRec v ix)
  Ast.AstLetHFunIn var f v ->
    astLetHFunIn var f (astIndexRec v ix)
  Ast.AstRFromS @sh t ->
    let (takeSh, dropSh) = splitAt (valueOf @m) (Sh.shapeT @sh)
    in Sh.withShapeP takeSh $ \(Proxy @p_take) ->
       Sh.withShapeP dropSh $ \(Proxy @p_drop) ->
       gcastWith (unsafeCoerce Refl :: sh :~: p_take Sh.++ p_drop) $
       gcastWith (unsafeCoerce Refl :: Sh.Rank p_drop :~: n) $
       astRFromS $ astIndexStepS @p_take @p_drop
                                 t (ShapedList.listToSized $ indexToList ix)
  Ast.AstConstant v -> Ast.AstConstant $ astIndex v ix
  Ast.AstPrimalPart{} -> Ast.AstIndex v0 ix  -- must be a NF
  Ast.AstDualPart{} -> Ast.AstIndex v0 ix
  Ast.AstD u u' ->
    shareIx ix $ \ix2 -> Ast.AstD (astIndexRec u ix2) (astIndexRec u' ix2)

astIndexSOrStepOnly
  :: forall shm shn s r.
     ( Sh.Shape shm, Sh.Shape shn, Sh.Shape (shm Sh.++ shn)
     , GoodScalar r, AstSpan s )
  => Bool -> AstShaped s r (shm Sh.++ shn) -> AstIndexS shm
  -> AstShaped s r shn
astIndexSOrStepOnly stepOnly (Ast.AstIndexS v ix) ZS =
  astIndexSOrStepOnly stepOnly v ix
astIndexSOrStepOnly _ v0 ZS = v0
astIndexSOrStepOnly stepOnly v0 ix@((::$) @in1 i1 (rest1 :: AstIndexS shm1)) =
  let astIndexRec, astIndex
        :: forall shm' shn' s'.
           ( Sh.Shape shm', Sh.Shape shn', Sh.Shape (shm' Sh.++ shn')
           , AstSpan s' )
        => AstShaped s' r (shm' Sh.++ shn') -> AstIndexS shm'
        -> AstShaped s' r shn'
      astIndexRec vRec ZS = vRec
      astIndexRec vRec ixRec =
        if stepOnly then Ast.AstIndexS vRec ixRec else astIndexS vRec ixRec
      astIndex = if stepOnly then astIndexStepS else astIndexS
      astGather
        :: forall shm' shn' p'.
           ( Sh.Shape shm', Sh.Shape shn'
           , Sh.Shape (Sh.Take p' shm'), Sh.Shape (Sh.Drop p' shm') )
        => AstShaped s r shm'
        -> (AstVarListS shn', AstIndexS (Sh.Take p' shm'))
        -> AstShaped s r (shn' Sh.++ Sh.Drop p' shm')
      astGather = if stepOnly then astGatherStepS else astGatherS
 in case v0 of
  Ast.AstVarS{} -> Ast.AstIndexS v0 ix
  Ast.AstLetS var u v -> astLetS var u (astIndexRec v ix)
  Ast.AstLetADShareS{} -> error "astIndexROrStepOnlyS: AstLetADShareS"
  Ast.AstCondS b v w ->
    shareIxS ix $ \ix2 -> astCondS b (astIndexRec v ix2) (astIndexRec w ix2)
  Ast.AstMinIndexS @shz @n1 v ->
    Sh.withShapeP (drop 1 (Sh.shapeT @shn)
                   ++ [last (Sh.shapeT @shz)]) $ \(Proxy @shd) ->
      gcastWith (unsafeCoerce Refl
                 :: Sh.Drop 1 shn Sh.++ '[Sh.Last shz] :~: shd) $
      withSNat (Sh.shapeT @shn !! 0) $ \(SNat @i0shn) ->
        gcastWith (unsafeCoerce Refl :: Sh.Index shn 0 :~: i0shn) $
        gcastWith (unsafeCoerce Refl
                   :: Sh.Index shn 0 ': Sh.Drop 1 shn :~: shn) $
        gcastWith (unsafeCoerce Refl
                   :: Sh.Init (shn Sh.++ '[Sh.Last shz]) :~: shn) $
        gcastWith (unsafeCoerce Refl
                   :: shm Sh.++ (shn Sh.++ '[Sh.Last shz]) :~: n1 ': shz) $
        Ast.AstMinIndexS @(Sh.Drop 1 shn Sh.++ '[Sh.Last shz]) @(Sh.Index shn 0)
        $ astIndexSOrStepOnly @shm @(shn Sh.++ '[Sh.Last shz]) stepOnly v ix
  Ast.AstMaxIndexS @shz @n1 v ->
    Sh.withShapeP (drop 1 (Sh.shapeT @shn)
                   ++ [last (Sh.shapeT @shz)]) $ \(Proxy @shd) ->
      gcastWith (unsafeCoerce Refl
                 :: Sh.Drop 1 shn Sh.++ '[Sh.Last shz] :~: shd) $
      withSNat (Sh.shapeT @shn !! 0) $ \(SNat @i0shn) ->
        gcastWith (unsafeCoerce Refl :: Sh.Index shn 0 :~: i0shn) $
        gcastWith (unsafeCoerce Refl
                   :: Sh.Index shn 0 ': Sh.Drop 1 shn :~: shn) $
        gcastWith (unsafeCoerce Refl
                   :: Sh.Init (shn Sh.++ '[Sh.Last shz]) :~: shn) $
        gcastWith (unsafeCoerce Refl
                   :: shm Sh.++ (shn Sh.++ '[Sh.Last shz]) :~: n1 ': shz) $
        Ast.AstMaxIndexS @(Sh.Drop 1 shn Sh.++ '[Sh.Last shz]) @(Sh.Index shn 0)
        $ astIndexSOrStepOnly @shm @(shn Sh.++ '[Sh.Last shz]) stepOnly v ix
  Ast.AstFloorS v -> Ast.AstFloorS $ astIndexSOrStepOnly stepOnly v ix
  Ast.AstIotaS | AstConst i <- i1 -> fromIntegral i
  Ast.AstIotaS -> Ast.AstIndexS v0 ix
  AstN1S opCode u ->
    shareIxS ix $ \ix2 -> AstN1S opCode (astIndexRec u ix2)
  AstN2S opCode u v ->
    shareIxS ix $ \ix2 -> AstN2S opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstR1S opCode u ->
    shareIxS ix
    $ \ix2 -> Ast.AstR1S opCode (astIndexRec u ix2)
  Ast.AstR2S opCode u v ->
    shareIxS ix
    $ \ix2 -> Ast.AstR2S opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstI2S opCode u v ->
    shareIxS ix
    $ \ix2 -> Ast.AstI2S opCode (astIndexRec u ix2) (astIndexRec v ix2)
  AstSumOfListS args ->
    shareIxS ix $ \ix2 -> astSumOfListS (map (`astIndexRec` ix2) args)
  Ast.AstIndexS v (ix2 :: AstIndexS sh4) ->
    gcastWith (unsafeCoerce Refl
               :: (sh4 Sh.++ shm) Sh.++ shn :~: sh4 Sh.++ (shm Sh.++ shn)) $
    Sh.withShapeP (Sh.shapeT @sh4 ++ Sh.shapeT @shm) $ \(Proxy @sh41) ->
      gcastWith (unsafeCoerce Refl :: sh4 Sh.++ shm :~: sh41) $
      astIndexS v (ShapedList.appendSized ix2 ix)
  Ast.AstSumS @n1 v ->
    let perm3 = backpermCycle $ length (Sh.shapeT @shm) + 1
    in Sh.withShapeP (Sh.shapeT @shm
                      ++ (valueOf @n1 : Sh.shapeT @shn)) $ \(Proxy @sm1n) ->
      gcastWith (unsafeCoerce Refl :: shm Sh.++ (n1 : shn) :~: sm1n) $
      withSNat (1 + length (Sh.shapeT @shn)
                + length (Sh.shapeT @shm)) $ \(SNat @r1mn) ->
        gcastWith (unsafeCoerce Refl :: Sh.Rank (n1 : shm Sh.++ shn) :~: r1mn) $
        Sh.withShapeP perm3 $ \(Proxy @perm3P) ->
          gcastWith (unsafeCoerce Refl
                     :: Compare (OS.Rank perm3P) (Sh.Rank (n1 : shm Sh.++ shn))
                        :~: LT) $
          gcastWith (unsafeCoerce Refl
                     :: Sh.Permute perm3P (n1 : (shm Sh.++ shn))
                        :~: shm Sh.++ (n1 : shn)) $
          trustMeThisIsAPermutation @perm3P $
          astSumS $ astIndex @shm @(n1 : shn)
                             (astTransposeS @perm3P @(n1 : shm Sh.++ shn) v)
                             ix
-- TODO:
--  Ast.AstScatterS @sh2 @p7 @sh7
--                  v (vars, AstIntVar var5 ::$ (ix2 :: AstIndexS p71))
--    | AstIntVar var6 <- i1, var6 == var5 ->
--        gcastWith (unsafeCoerce Refl
--                   :: shm1 Sh.++ shn :~: p71 Sh.++ Sh.Drop p7 sh7) $
--        astIndex (astScatterS @_ @_ @sh7 v (vars, ix2)) rest1
--  Ast.AstScatter @_ @n7 (_ :$: sh)
--                 v (vars, AstConst i5 :.: (ix2 :: AstIndex p71))
--    | AstConst i6 <- i1 ->
--        gcastWith (unsafeCoerce Refl :: m1 + n :~: p71 + n7) $
--        if i6 == i5
--        then astIndex (astScatter sh v (vars, ix2)) rest1
--        else astIndex (astReplicate0N @(m1 + n) sh 0) rest1
  -- AstScatter sh v (vars2, ZIR) ->
  --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZIR)
  Ast.AstScatterS{} ->  -- normal form
    Ast.AstIndexS v0 ix
  Ast.AstFromListS l | AstConst it <- i1 ->
    let i = fromIntegral $ OR.unScalar it
    in astIndex (if 0 <= i && i < length l
                 then l !! i
                 else astReplicate0NS @(shm1 Sh.++ shn) 0) rest1

  Ast.AstFromListS{} | ZS <- rest1 ->  -- normal form
    Ast.AstIndexS v0 ix
  Ast.AstFromListS l ->
    shareIxS rest1 $ \ix2 ->
      Ast.AstIndexS @'[in1] @shn (astFromListS $ map (`astIndexRec` ix2) l)
                    (ShapedList.singletonShaped i1)
  Ast.AstFromVectorS l | AstConst it <- i1 ->
    let i = fromIntegral $ OR.unScalar it
    in astIndex (if 0 <= i && i < V.length l
                 then l V.! i
                 else astReplicate0NS @(shm1 Sh.++ shn) 0) rest1
  Ast.AstFromVectorS{} | ZS <- rest1 ->  -- normal form
    Ast.AstIndexS v0 ix
  Ast.AstFromVectorS l ->
    shareIxS rest1 $ \ix2 ->
      Ast.AstIndexS @'[in1] @shn (astFromVectorS $ V.map (`astIndexRec` ix2) l)
                    (ShapedList.singletonShaped i1)
  Ast.AstReplicateS v ->
    astIndex v rest1
  Ast.AstAppendS @n3 @m3 u v | AstConst it <- i1 ->
    let i = fromIntegral $ OR.unScalar it
        len = valueOf @m3 :: Int
    in if len > i
       then astIndex @(m3 ': shm1) u (i1 ::$ rest1)
       else astIndex @(n3 ': shm1)
                     v (simplifyAst (i1 - fromIntegral len) ::$ rest1)
  Ast.AstAppendS{} ->  -- normal form
    Ast.AstIndexS v0 ix
  Ast.AstSliceS @i v ->
    let ii = simplifyAst (i1 + fromIntegral (valueOf @i :: Int))
      -- we generate this index, so we simplify on the spot
    in astIndex v (ii ::$ rest1)
  Ast.AstReverseS v ->
    let iRev = simplifyAst (fromIntegral (valueOf @in1 - 1 :: Int) - i1)
      -- we generate this index, so we simplify on the spot
    in astIndex v (iRev ::$ rest1)
  Ast.AstTransposeS @perm @sh2 v
    | length (Sh.shapeT @shm) >= length (Sh.shapeT @perm) ->
      Sh.withShapeP
        (permutePrefixList (Sh.shapeT @perm)
                           (Sh.shapeT @shm)) $ \(Proxy @shmPerm) ->
          gcastWith (unsafeCoerce Refl :: shm :~: Sh.Permute perm shmPerm) $
          let ix2 :: AstIndexS shmPerm =
                ShapedList.permutePrefixShaped @perm ix
          in gcastWith (unsafeCoerce Refl :: sh2 :~: shmPerm Sh.++ shn) $
             astIndex @shmPerm v ix2
  Ast.AstTransposeS @perm v ->
    astIndex (astTransposeAsGatherS @perm v) ix
  Ast.AstReshapeS v ->
    astIndex (astReshapeAsGatherS v) ix
  Ast.AstBuild1S (var2, v) ->
    withListSh (Proxy @(shm1 Sh.++ shn)) $ \_ ->
      astIndex (astSFromR @(shm1 Sh.++ shn) $ astLet var2 i1 $ astRFromS v)
               rest1
      -- this uses astLet, because the index integers are ranked
  Ast.AstGatherS @_ @p @sh v (ZS, ix2) ->
    Sh.withShapeP (Sh.shapeT @(Sh.Take p sh) ++ Sh.shapeT @shm)
    $ \(Proxy @sh1n) ->
      gcastWith (unsafeCoerce Refl :: (Sh.Take p sh Sh.++ shm :~: sh1n)) $
      gcastWith (unsafeCoerce Refl :: Sh.Take p sh Sh.++ shm Sh.++ shn :~: sh) $
        -- TODO: why is this needed? if it's true (it is), GHC should know it
      astIndex v (ShapedList.appendSized ix2 ix)
  Ast.AstGatherS v (var2 ::$ (vars :: AstVarListS shm71), ix2) ->
    withListSh (Proxy @shn) $ \_ ->
      Sh.withShapeP (Sh.shapeT @shm1 ++ Sh.shapeT @shn) $ \(Proxy @sh1n) ->
        gcastWith (unsafeCoerce Refl :: shm1 Sh.++ shn :~: sh1n) $
        let w :: AstShaped s r (shm1 Sh.++ shn)
            w = astGather v (vars, ix2)
        in astSFromR $ astLet var2 i1 $ astRFromS $ astIndexS @shm1 @shn w rest1
      -- this uses astLet, because the index integers are ranked
  Ast.AstCastS t -> astCastS $ astIndexSOrStepOnly stepOnly t ix
  Ast.AstFromIntegralS v -> astFromIntegralS $ astIndexSOrStepOnly stepOnly v ix
  AstConstS t ->
    let unConst :: AstRanked PrimalSpan Int64 0 -> Maybe [OR.Array 0 Int64]
                -> Maybe [OR.Array 0 Int64]
        unConst (AstConst i) (Just l) = Just $ i : l
        unConst _ _ = Nothing
    in case foldr unConst (Just []) ix of
      Just ixInt -> AstConstS $ tindexZSR t $ ShapedList.listToSized @shm
                    $ map OR.unScalar ixInt
        -- TODO: we'd need mapM for Index to keep this rank-typed
      Nothing -> Ast.AstIndexS v0 ix
  Ast.AstLetHVectorInS vars l v ->
    astLetHVectorInS vars l (astIndexRec v ix)
  Ast.AstLetHFunInS var f v ->
    astLetHFunInS var f (astIndexRec v ix)
  Ast.AstSFromR @sh t ->
    withListSh (Proxy @shn) $ \_ ->
      gcastWith (unsafeCoerce Refl
                 :: Sh.Rank shm + Sh.Rank shn :~: Sh.Rank (shm Sh.++ shn)) $
                      -- reversing this equality causes " Could not deduce
                      -- ‘KnownNat (OS.Rank sh1)’ error, but this is
                      -- probably ~fine and maybe caused by KnownNat.Solver
      astSFromR $ astIndexStep t (ShapedList.shapedToIndex ix)
  Ast.AstConstantS v -> Ast.AstConstantS $ astIndex v ix
  Ast.AstPrimalPartS{} -> Ast.AstIndexS v0 ix  -- must be a NF
  Ast.AstDualPartS{} -> Ast.AstIndexS v0 ix
  Ast.AstDS u u' ->
    shareIxS ix $ \ix2 -> Ast.AstDS (astIndexRec u ix2) (astIndexRec u' ix2)

-- TODO: compared to rletIx, it adds many lets, not one, but does not
-- create other (and non-simplified!) big terms and also uses astIsSmall,
-- so it's probably more efficient. Use this instead of rletIx/sletIx
-- or design something even better.
shareIx :: (KnownNat n, KnownNat m)
        => AstIndex n -> (AstIndex n -> AstRanked s r m) -> AstRanked s r m
{-# NOINLINE shareIx #-}
shareIx ix f = unsafePerformIO $ do
  let shareI :: AstRanked PrimalSpan Int64 0
             -> IO ( Maybe (IntVarName, AstRanked PrimalSpan Int64 0)
                   , AstRanked PrimalSpan Int64 0 )
      shareI i | astIsSmall True i = return (Nothing, i)
      shareI i = funToAstIntVarIO $ \ (!varFresh, !astVarFresh) ->
                   (Just (varFresh, i), astVarFresh)
  (bindings, ix2) <- mapAndUnzipM shareI (indexToList ix)
  return $! foldr (uncurry Ast.AstLet) (f $ listToIndex ix2)
                                       (catMaybes bindings)

shareIxS :: -- (Sh.Shape shn, Sh.Shape shm)
            AstIndexS shn -> (AstIndexS shn -> AstShaped s r shm)
         -> AstShaped s r shm
{-# NOINLINE shareIxS #-}
shareIxS ix f = f ix
  -- TODO (Ast.AstLetS is not general enough, we'd need to convert)

astGatherR
  :: forall m n p s r.
     (KnownNat m, KnownNat p, KnownNat n, GoodScalar r, AstSpan s)
  => ShapeInt (m + n) -> AstRanked s r (p + n) -> (AstVarList m, AstIndex p)
  -> AstRanked s r (m + n)
astGatherR = astGatherROrStepOnly False

astGatherS
  :: forall sh2 p sh s r.
     ( Sh.Shape sh, Sh.Shape sh2
     , Sh.Shape (Sh.Take p sh), Sh.Shape (Sh.Drop p sh) )
  => AstShaped s r sh
  -> (AstVarListS sh2, AstIndexS (Sh.Take p sh))
  -> AstShaped s r (sh2 Sh.++ Sh.Drop p sh)
astGatherS v (vars, ix) = Ast.AstGatherS v (vars, ix)  -- TODO

astGatherStep
  :: forall m n p s r.
     (KnownNat m, KnownNat p, KnownNat n, GoodScalar r, AstSpan s)
  => ShapeInt (m + n) -> AstRanked s r (p + n) -> (AstVarList m, AstIndex p)
  -> AstRanked s r (m + n)
astGatherStep sh v (vars, ix) =
  astGatherROrStepOnly True sh (simplifyStepNonIndex v)
                       (vars, fmap simplifyAst ix)

astGatherStepS
  :: forall sh2 p sh s r.
     ( Sh.Shape sh, Sh.Shape sh2
     , Sh.Shape (Sh.Take p sh), Sh.Shape (Sh.Drop p sh) )
  => AstShaped s r sh
  -> (AstVarListS sh2, AstIndexS (Sh.Take p sh))
  -> AstShaped s r (sh2 Sh.++ Sh.Drop p sh)
-- TODO: this probably needs an extra condition similar to kN == vkN below
--astGatherStepS v (AstVarName varId ::$ ZS, AstIntVarS varId2 ::$ ZS)
--  | varId == varId2 = ...
astGatherStepS v (vars, ix) = Ast.AstGatherS v (vars, ix)  -- TODO

-- Assumption: vars0 don't not occur in v0. The assumption only holds
-- when newly generated variables are fresh, which is the case as long
-- as resetVarCounter is not used. The assumption makes it easier to spot
-- bugs or corruption, hence we assert it in the code below.
--
-- The v0 term is already at least one step simplified,
-- either from full recursive simplification or from astGatherStep.
astGatherROrStepOnly
  :: forall m n p s r.
     (KnownNat m, KnownNat p, KnownNat n, GoodScalar r, AstSpan s)
  => Bool -> ShapeInt (m + n) -> AstRanked s r (p + n)
  -> (AstVarList m, AstIndex p)
  -> AstRanked s r (m + n)
astGatherROrStepOnly stepOnly sh0 v0 (vars0, ix0) =
  case (sh0, (vars0, ix0)) of
    _ | any (`varNameInAst` v0) vars0 ->
      error $ "astGather: gather vars in v0: "
              ++ show (vars0, v0)
    (_, (ZR, _)) -> astIndex v0 ix0
    (sh, (_, ZIR)) -> astReplicateN sh v0
    (k :$: sh', (AstVarName varId ::: vars, i1 :.: rest1)) ->
      if | not (any (`varNameInAst` i1) vars0) ->
           astGatherROrStepOnly stepOnly sh0 (astIndex v0 (i1 :.: ZIR))
                                (vars0, rest1)
         | case iN of
             AstIntVar varN' ->
               varN' == varN
               && not (any (varN `varNameInAst`) restN)
               && case ( dropShape @(m - 1) sh0
                       , dropShape @(p - 1) (shapeAst v0) ) of
                 (kN :$: _, vkN :$: _) -> kN == vkN
                 _ -> error "impossible pattern needlessly required"
             _ -> False
           -> astGatherROrStepOnly stepOnly sh0 v0 (varsN, restN)
         | varInIndex varId ix0 ->
           astGatherCase sh0 v0 (vars0, ix0)
         | otherwise ->
           astReplicate k (astGatherROrStepOnly stepOnly sh' v0 (vars, ix0))
       where
        (restN, iN) = unsnocIndex1 ix0
        (varsN, varN) = unsnocSized1 vars0
    _ ->
      error "astGather: impossible pattern needlessly required"
 where
  astIndex :: forall m' n' s'. (KnownNat m', KnownNat n', AstSpan s')
           => AstRanked s' r (m' + n') -> AstIndex m' -> AstRanked s' r n'
  astIndex = if stepOnly then astIndexStep else astIndexR
  astGatherRec, astGather
    :: forall m' n' p' s' r'.
       (KnownNat m', KnownNat p', KnownNat n', AstSpan s', GoodScalar r')
    => ShapeInt (m' + n') -> AstRanked s' r' (p' + n')
    -> (AstVarList m', AstIndex p')
    -> AstRanked s' r' (m' + n')
  astGatherRec = if stepOnly then Ast.AstGather else astGatherR
  astGather = if stepOnly then astGatherStep else astGatherR
  -- Note that v4 is in weak head normal form and so can't one-step reduce
  -- and so we don't have to reduce it to expose any top redexes.
  astGatherCase
    :: forall m' n' p' r'.
       (KnownNat m', KnownNat p', KnownNat n', GoodScalar r')
    => ShapeInt (m' + n') -> AstRanked s r' (p' + n')
    -> (AstVarList m', AstIndex p')
    -> AstRanked s r' (m' + n')
  astGatherCase sh4 v4 (_, ZIR) = astReplicateN sh4 v4  -- not really possible
  astGatherCase sh4 v4 ( vars4
                       , ix4@(i4 :.: (rest4 :: AstIndex p1')) ) = case v4 of
    Ast.AstVar{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstLet var u v -> astLet var u (astGatherCase sh4 v (vars4, ix4))
    Ast.AstLetADShare{} -> error "astGatherCase: AstLetADShare"
    Ast.AstCond b v w -> astCond b (astGather sh4 v (vars4, ix4))
                                   (astGather sh4 w (vars4, ix4))
    Ast.AstMinIndex v ->
      Ast.AstMinIndex
      $ astGatherROrStepOnly stepOnly
          (sh4 `appendShape` singletonShape (lastShape (shapeAst v)))
          v (vars4, ix4)
    Ast.AstMaxIndex v ->
      Ast.AstMaxIndex
      $ astGatherROrStepOnly stepOnly
          (sh4 `appendShape` singletonShape (lastShape (shapeAst v)))
          v (vars4, ix4)
    Ast.AstFloor v ->
      Ast.AstFloor
      $ astGatherROrStepOnly stepOnly sh4 v (vars4, ix4)
    Ast.AstIota | AstConst i <- i4 -> case sameNat (Proxy @p') (Proxy @1) of
      Just Refl -> astReplicate0N sh4 $ fromIntegral i
      _ -> error "astGather: AstIota: impossible pattern needlessly required"
    Ast.AstIota ->  -- probably nothing can be simplified; a normal form
      Ast.AstGather sh4 v4 (vars4, ix4)
    AstN1 opCode v | not (isVar v) ->
      AstN1 opCode (astGatherRec sh4 v (vars4, ix4))
    AstN1{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    AstN2{} -> Ast.AstGather sh4 v4 (vars4, ix4)
      -- Going inside AstN2 usually makes the term more expensive to interpret
      -- and reverting this transformation requires comparing two arguments,
      -- so it's not practical.
    Ast.AstR1 opCode v | not (isVar v) ->
      Ast.AstR1 opCode (astGatherRec sh4 v (vars4, ix4))
    Ast.AstR1{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstR2{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstI2{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    AstSumOfList{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstIndex v2 ix2 -> case (v2, ix2) of
      (Ast.AstFromList{}, i2 :.: ZIR) -> astGather sh4 v2 (vars4, i2 :.: ix4)
      (Ast.AstFromVector{}, i2 :.: ZIR) -> astGather sh4 v2 (vars4, i2 :.: ix4)
      _ ->  -- AstVar, AstConst
        Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstSum v ->
      let perm3 = backpermCycle $ valueOf @p' + 1
          perm4 = permCycle $ valueOf @m' + 1
          (sh41, sh42) = splitAt_Shape @m' sh4
          sh5 = appendShape sh41 (lengthAst v :$: sh42)
      in astSum $ astTransposeAsGather perm4  -- TODO: inline and simplify less
         $ astGather sh5 (astTransposeAsGather perm3 v) (vars4, ix4)
             -- TODO: why is simplification not idempotent without AsGather?
    Ast.AstScatter @_ @n7 (_ :$: sh)
                   v (vars, AstIntVar var5 :.: (ix2 :: AstIndex p71))
      | AstIntVar var6 <- i4, var6 == var5 ->
          gcastWith (unsafeCoerce Refl :: p1' + n' :~: p71 + n7) $
          astGather sh4 (astScatter sh v (vars, ix2))
                        (vars4, rest4)
    Ast.AstScatter @_ @n7 (_ :$: sh)
                   v (vars, AstConst i5 :.: (ix2 :: AstIndex p71))
      | AstConst i6 <- i4 ->
          gcastWith (unsafeCoerce Refl :: p1' + n' :~: p71 + n7) $
          if i6 == i5
          then astGather sh4 (astScatter sh v (vars, ix2)) (vars4, rest4)
          else astGather sh4 (astReplicate0N sh 0) (vars4, rest4)
    Ast.AstScatter{} ->  -- normal form
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstFromList l | AstConst it <- i4 ->
      let i = fromIntegral $ OR.unScalar it
      in astGather sh4 (if 0 <= i && i < length l
                        then l !! i
                        else astReplicate0N @(p1' + n')
                                            (dropShape $ shapeAst v4) 0)
                       (vars4, rest4)
    Ast.AstFromList{} | gatherFromNF vars4 ix4 ->  -- normal form
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstFromList l ->
      -- Term rest4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use rlet.
      funToVarsIx (valueOf @m') $ \ (!varsFresh, !ixFresh) ->
        let f v = astGatherRec sh4 v (vars4, rest4)
            -- This subst doesn't currently break sharing because it's a rename.
            subst i =
              foldr (uncurry substituteAst) i
                    (zipSized (fmap (SubstitutionPayloadRanked
                                       @PrimalSpan @Int64)
                               $ indexToSized ixFresh) vars4)
            i5 = subst i4
        in astGather sh4 (astFromList $ map f l) (varsFresh, i5 :.: ixFresh)
    Ast.AstFromVector l | AstConst it <- i4 ->
      let i = fromIntegral $ OR.unScalar it
      in astGather sh4 (if 0 <= i && i < V.length l
                        then l V.! i
                        else astReplicate0N @(p1' + n')
                                            (dropShape $ shapeAst v4) 0)
                       (vars4, rest4)
    Ast.AstFromVector{} | gatherFromNF vars4 ix4 ->  -- normal form
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstFromVector l ->
      -- Term rest4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use rlet.
      funToVarsIx (valueOf @m') $ \ (!varsFresh, !ixFresh) ->
        let f v = astGatherRec sh4 v (vars4, rest4)
            -- This subst doesn't currently break sharing because it's a rename.
            subst i =
              foldr (uncurry substituteAst) i
                    (zipSized (fmap (SubstitutionPayloadRanked
                                       @PrimalSpan @Int64)
                               $ indexToSized ixFresh) vars4)
            i5 = subst i4
       in astGather sh4 (astFromVector $ V.map f l) (varsFresh, i5 :.: ixFresh)
    Ast.AstReplicate _k v -> astGather sh4 v (vars4, rest4)
    Ast.AstAppend u v | AstConst it <- i4 ->
      let i = fromIntegral $ OR.unScalar it
          len = lengthAst u
      in if len > i
         then astGather sh4 u (vars4, ix4)
         else astGather sh4 v
                        (vars4, simplifyAst (i4 - fromIntegral len) :.: rest4)
    Ast.AstAppend{} ->  -- normal form
      {- This is wrong, see astIndexROrStepOnly:
         We can't express append as gather, because AstFromList needs
         arguments of the same shape, so here we need to inline a lot of code.
         TODO: The normal form is not acceptable, because fusion is halted
         and can't get inside AstAppend, unlike inside AstFromList.
         Let's see if we can do the same trick as with AstFromList
         and get all the remaining indexes inside AstGather.
         BTW, probably fusion is halted also due to NF with AstScatter.
      let vlen = AstConst $ lengthAst v
          iw = simplifyAst (AstIntOp MinusIntOp [i4, vlen])
          v2 = astGatherRec sh4 v (vars4, i4 :.: rest4)
          w2 = astGatherRec sh4 w (vars4, iw :.: rest4)
      in case simplifyAstBool $ AstRelInt LsOp [i4, vlen] of
        AstBoolConst b -> if b
                          then astGather sh4 v (vars4, i4 :.: rest4)
                          else astGather sh4 w (vars4, iw :.: rest4)
        b -> astGather sh4 (astFromList [v2, w2])
                       (vars4, AstIntCond b 0 1
                               :.: sizedToIndex (fmap AstIntVar vars4))
      -}
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstSlice i _k v ->
      let ii = simplifyAst (i4 + fromIntegral i)
        -- we generate this index, so we simplify on the spot
      in astGather sh4 v (vars4, ii :.: rest4)
    Ast.AstReverse v ->
      let iRev = simplifyAst (fromIntegral (lengthAst v - 1) - i4)
        -- we generate this index, so we simplify on the spot
      in astGather sh4 v (vars4, iRev :.: rest4)
    Ast.AstTranspose perm v | valueOf @p' >= length perm ->
      astGather sh4 v (vars4, permutePrefixIndex perm ix4)
    Ast.AstTranspose perm v ->
      astGather sh4 (astTransposeAsGather perm v) (vars4, ix4)
    Ast.AstReshape sh v ->
      astGather sh4 (astReshapeAsGather sh v) (vars4, ix4)
    Ast.AstBuild1{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstGather @m2 @n2 _sh2 v2 (vars2, ix2) ->
      -- Term ix4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use rlet.
      --
      -- Independently, we need to insert lets to each index element,
      -- bloating the term. TODO: would going via a rank 1 vector,
      -- as in rletIx help or would we need to switch indexes to vector
      -- altogether (terrible for user comfort, especially wrt typing).
      let substLet :: AstIndex m7 -> AstVarList m7 -> AstInt -> AstInt
          substLet ix vars i =
            simplifyAst  -- we generate this index, so we simplify on the spot
            $ foldr (uncurry astLetInt) i
                    (zipSized vars (indexToSized ix))
          composedGather :: p' <= m2 => AstRanked s r' (m' + n')
          composedGather =
            let (vars2p, vars22) = splitAt_Sized @p' @(m2 - p') vars2
                ix22 = fmap (substLet ix4 vars2p) ix2
            in gcastWith (unsafeCoerce Refl :: m2 + n2 - p' :~: n')
               $ astGather sh4 v2 (appendSized vars4 vars22, ix22)
          assimilatedGather :: m2 <= p' => AstRanked s r' (m' + n')
          assimilatedGather =
            let (ix42, ix44) = splitAt_Index @m2 @(p' - m2) ix4
                ix22 = fmap (substLet ix42 vars2) ix2
            in gcastWith (unsafeCoerce Refl :: n' + p' - m2 :~: n2)
               $ astGather sh4 v2 (vars4, appendIndex ix22 ix44)
      in case cmpNat (Proxy @p') (Proxy @m2) of
        LTI -> composedGather
        EQI -> assimilatedGather
        GTI -> gcastWith (flipCompare @p' @m2) assimilatedGather
    Ast.AstCast v -> astCast $ astGather sh4 v (vars4, ix4)
    Ast.AstFromIntegral v -> astFromIntegral $ astGather sh4 v (vars4, ix4)
    AstConst{} ->  -- free variables possible, so can't compute the tensor
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstLetHVectorIn vars l v ->
      astLetHVectorIn vars l (astGatherCase sh4 v (vars4, ix4))
    Ast.AstLetHFunIn var f v ->
      astLetHFunIn var f (astGatherCase sh4 v (vars4, ix4))
    Ast.AstRFromS{} {- @sh v -} -> Ast.AstGather sh4 v4 (vars4, ix4)
      -- TODO: this is broken
      {-
      let (takeSh, dropSh) = splitAt (valueOf @p') (Sh.shapeT @sh)
      in Sh.withShapeP takeSh $ \(Proxy @p_take) ->
         Sh.withShapeP dropSh $ \(Proxy @p_drop) ->
         gcastWith (unsafeCoerce Refl :: sh :~: p_take Sh.++ p_drop) $
         gcastWith (unsafeCoerce Refl :: p_take :~: Sh.Take p' sh) $
         gcastWith (unsafeCoerce Refl :: p_drop :~: Sh.Drop p' sh) $
         gcastWith (unsafeCoerce Refl :: Sh.Rank sh :~: p' + n') $
         astRFromS $ astGatherStepS @_ @p' @sh v
                     ( ShapedList.listToSized $ sizedToList vars4
                     , ShapedList.listToSized $ indexToList ix4 ) -}
    Ast.AstConstant v ->
      Ast.AstConstant
      $ (if stepOnly then astGatherStep else astGatherR) sh4 v (vars4, ix4)
    Ast.AstPrimalPart{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstDualPart{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstD u u' ->
      -- Term ix4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use rlet.
      -- Also, the sharing would be dissolved by the substitution, anyway,
      -- and the same subsitution would be unsound with sharing.
      funToVarsIx (valueOf @m') $ \ (!varsFresh, !ixFresh) ->
        -- This subst doesn't currently break sharing, because it's a rename.
        let subst i =
              foldr (uncurry substituteAst) i
                    (zipSized (fmap (SubstitutionPayloadRanked
                                       @PrimalSpan @Int64)
                               $ indexToSized ixFresh)
                              vars4)
            ix5 = fmap subst ix4
        in Ast.AstD (astGatherRec sh4 u (vars4, ix4))
                    (astGatherRec sh4 u' (varsFresh, ix5))

gatherFromNF :: forall m p. (KnownNat m, KnownNat p)
             => AstVarList m -> AstIndex (1 + p) -> Bool
gatherFromNF _ ZIR = error "gatherFromNF: impossible pattern needlessly required"
gatherFromNF vars (i :.: rest) = case cmpNat (Proxy @p) (Proxy @m) of
  LTI ->
    let cmp (AstIntVar var1, AstIntVar var2) = var1 == var2
        cmp _ = False
        (varsP, varsPM) = splitAt_Sized @p @(m - p) vars
    in all cmp (zipIndex rest (sizedToIndex (fmap AstIntVar varsP)))
       && not (any (`varNameInAst` i) varsPM)
  EQI ->
    let cmp (AstIntVar var1, AstIntVar var2) = var1 == var2
        cmp _ = False
    in all cmp (zipIndex rest (sizedToIndex (fmap AstIntVar vars)))
  GTI -> False

flipCompare :: forall (a :: Nat) b. Compare a b ~ GT => Compare b a :~: LT
flipCompare = unsafeCoerce Refl

isVar :: AstRanked s r n -> Bool
isVar Ast.AstVar{} = True
isVar (Ast.AstConstant (Ast.AstVar{})) = True
isVar (Ast.AstPrimalPart (Ast.AstVar{})) = True
isVar (Ast.AstDualPart (Ast.AstVar{})) = True
isVar _ = False

isVarS :: AstShaped s r sh -> Bool
isVarS Ast.AstVarS{} = True
isVarS (Ast.AstConstantS (Ast.AstVarS{})) = True
isVarS (Ast.AstPrimalPartS (Ast.AstVarS{})) = True
isVarS (Ast.AstDualPartS (Ast.AstVarS{})) = True
isVarS _ = False

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
            | varInAst var i1 ->
                let w :: AstRanked s r (1 + n)
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
  => Int -> AstVarId -> AstRanked s r (1 + n) -> AstInt
  -> Maybe (AstRanked s r (1 + n))
gatherSimplify k var v0 i1 =
  case i1 of
    AstIntVar var2 | var2 == var ->
      Just $ astSliceLax 0 k v0
    AstIntOp PlusIntOp [AstIntVar var2, AstConst i2]
      | var2 == var ->
        Just $ astSliceLax i2 k v0
    AstIntOp PlusIntOp [AstConst i2, AstIntVar var2]
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
            => Int -> Int -> AstRanked s r (1 + n) -> AstRanked s r (1 + n)
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


-- * The simplifying combinators, one for each AST constructor

-- Inlining works for this let constructor, because it has just one variable,
-- unlike astLetHVectorIn, etc., so we don't try to eliminate it.
astLet :: forall n m r r2 s s2.
          ( KnownNat m, KnownNat n, GoodScalar r, GoodScalar r2
          , AstSpan s, AstSpan s2 )
       => AstVarName (AstRanked s) r n
       -> AstRanked s r n -> AstRanked s2 r2 m
       -> AstRanked s2 r2 m
astLet var u v | astIsSmall True u =
  substituteAst (SubstitutionPayloadRanked u) var v
astLet var u v@(Ast.AstVar _ var2) =
  if fromEnum var2 == fromEnum var
  then case sameAstSpan @s @s2 of
    Just Refl -> case sameNat (Proxy @n) (Proxy @m) of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> u
        _ -> error "astLet: scalar mismatch"
      _ -> error "astLet: rank mismatch"
    _ -> error "astLet: span mismatch"
  else v
astLet var u v@(Ast.AstConstant (Ast.AstVar _ var2)) =  -- a common noop
  if fromEnum var2 == fromEnum var
  then case sameAstSpan @s @PrimalSpan of
    Just Refl -> case sameNat (Proxy @n) (Proxy @m) of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> Ast.AstConstant u
        _ -> error "astLet: scalar mismatch"
      _ -> error "astLet: rank mismatch"
    _ -> error "astLet: span mismatch"
  else v
astLet var u v@(Ast.AstPrimalPart (Ast.AstVar _ var2)) =  -- a common noop
  if fromEnum var2 == fromEnum var
  then case sameAstSpan @s @FullSpan of
    Just Refl -> case sameNat (Proxy @n) (Proxy @m) of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> astPrimalPart @r2 u
        _ -> error "astLet: scalar mismatch"
      _ -> error "astLet: rank mismatch"
    _ -> error "astLet: span mismatch"
  else v
astLet var u v@(Ast.AstDualPart (Ast.AstVar _ var2)) =  -- a noop
  if fromEnum var2 == fromEnum var
  then case sameAstSpan @s @FullSpan of
    Just Refl -> case sameNat (Proxy @n) (Proxy @m) of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> astDualPart @r2 u
        _ -> error "astLet: scalar mismatch"
      _ -> error "astLet: rank mismatch"
    _ -> error "astLet: span mismatch"
  else v
astLet var (Ast.AstLetADShare l u) v
  | Just Refl <- sameAstSpan @s2 @PrimalSpan =
    Ast.AstLetADShare l $ Ast.AstLet var u v
astLet var u (Ast.AstLetADShare l v) | not (varNameInADShare var l) =
  Ast.AstLetADShare l $ Ast.AstLet var u v
astLet var u v = Ast.AstLet var u v

-- A special variant to bind integer expressions inside indexes.
-- It check if the bound variables appears in the body at all.
-- Normally, that's asymptotically worse than doing this
-- in a global inlining pass, but we assume indexes expressions
-- are short and we need them simple ASAP.
astLetInt :: AstVarName (AstRanked PrimalSpan) Int64 0
          -> AstRanked PrimalSpan Int64 0 -> AstRanked PrimalSpan Int64 0
          -> AstRanked PrimalSpan Int64 0
astLetInt var u v | var `varNameInAst` v = astLet var u v
astLetInt _ _ v = v

-- Inlining works for this let constructor, because it has just one variable,
-- unlike astLetHVectorIn, etc., so we don't try to eliminate it.
astLetS :: forall sh1 sh2 r r2 s s2.
           ( Sh.Shape sh1, Sh.Shape sh2, GoodScalar r, GoodScalar r2
           , AstSpan s, AstSpan s2 )
        => AstVarName (AstShaped s) r sh1
        -> AstShaped s r sh1 -> AstShaped s2 r2 sh2
        -> AstShaped s2 r2 sh2
astLetS var u v | astIsSmallS True u =
  substituteAstS (SubstitutionPayloadShaped u) var v
astLetS var u v@(Ast.AstVarS var2) =
  if fromEnum var2 == fromEnum var
  then case sameAstSpan @s @s2 of
    Just Refl -> case sameShape @sh1 @sh2 of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> u
        _ -> error "astLetS: scalar mismatch"
      _ -> error "astLetS: shape mismatch"
    _ -> error "astLetS: span mismatch"
  else v
astLetS var u v@(Ast.AstConstantS (Ast.AstVarS var2)) =  -- a common noop
  if fromEnum var2 == fromEnum var
  then case sameAstSpan @s @PrimalSpan of
    Just Refl -> case sameShape @sh1 @sh2 of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> Ast.AstConstantS u
        _ -> error "astLetS: scalar mismatch"
      _ -> error "astLetS: shape mismatch"
    _ -> error "astLetS: span mismatch"
  else v
astLetS var u v@(Ast.AstPrimalPartS (Ast.AstVarS var2)) =  -- a common noop
  if fromEnum var2 == fromEnum var
  then case sameAstSpan @s @FullSpan of
    Just Refl -> case sameShape @sh1 @sh2 of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> astPrimalPartS @r2 u
        _ -> error "astLetS: scalar mismatch"
      _ -> error "astLetS: shape mismatch"
    _ -> error "astLetS: span mismatch"
  else v
astLetS var u v@(Ast.AstDualPartS (Ast.AstVarS var2)) =  -- a noop
  if fromEnum var2 == fromEnum var
  then case sameAstSpan @s @FullSpan of
    Just Refl -> case sameShape @sh1 @sh2 of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> astDualPartS @r2 u
        _ -> error "astLetS: scalar mismatch"
      _ -> error "astLetS: shape mismatch"
    _ -> error "astLetS: span mismatch"
  else v
astLetS var (Ast.AstLetADShareS l u) v
  | Just Refl <- sameAstSpan @s2 @PrimalSpan =
    Ast.AstLetADShareS l $ Ast.AstLetS var u v
astLetS var u (Ast.AstLetADShareS l v) | not (varNameInADShare var l) =
  Ast.AstLetADShareS l $ Ast.AstLetS var u v
astLetS var u v = Ast.AstLetS var u v

astCond :: AstBool -> AstRanked s r n -> AstRanked s r n -> AstRanked s r n
astCond (AstBoolConst b) v w = if b then v else w
astCond b (Ast.AstConstant v) (Ast.AstConstant w) =
  Ast.AstConstant $ Ast.AstCond b v w
astCond b (Ast.AstLetADShare l v) w =
  Ast.AstLetADShare l $ Ast.AstCond b v w
astCond b v (Ast.AstLetADShare l w) =
  Ast.AstLetADShare l $ Ast.AstCond b v w
astCond b v w = Ast.AstCond b v w

astCondS :: AstBool -> AstShaped s r sh -> AstShaped s r sh -> AstShaped s r sh
astCondS (AstBoolConst b) v w = if b then v else w
astCondS b (Ast.AstConstantS v) (Ast.AstConstantS w) =
  Ast.AstConstantS $ Ast.AstCondS b v w
astCondS b (Ast.AstLetADShareS l v) w =
  Ast.AstLetADShareS l $ Ast.AstCondS b v w
astCondS b v (Ast.AstLetADShareS l w) =
  Ast.AstLetADShareS l $ Ast.AstCondS b v w
astCondS b v w = Ast.AstCondS b v w

astSumOfList :: (KnownNat n, GoodScalar r, AstSpan s)
             => [AstRanked s r n] -> AstRanked s r n
astSumOfList = foldr1 (+)  -- @sum@ breaks

astSumOfListS :: (Sh.Shape sh, GoodScalar r, AstSpan s)
              => [AstShaped s r sh] -> AstShaped s r sh
astSumOfListS = sum

astSum :: (KnownNat n, GoodScalar r, AstSpan s)
       => AstRanked s r (1 + n) -> AstRanked s r n
astSum t0 = case shapeAst t0 of
  0 :$: rest -> astReplicate0N rest 0
--  1 :$: rest -> astReshape rest t0  -- TODO: slows down the CNNO test
  _ -> case t0 of
    -- Ast.AstLet var u v -> astLet var u (astSum v)
    -- this is problematic, because it keeps huge tensors alive for longer;
    -- but for AstLetADShare it's usually fine, because they are often
    -- either global or duplicated and rarely local and unique
    -- and we prefer the global to duplicated
    Ast.AstLetADShare l v -> Ast.AstLetADShare l (astSum v)
    Ast.AstScatter (_ :$: sh) v (vars, _ :.: ix) -> astScatter sh v (vars, ix)
    Ast.AstFromList l -> astSumOfList l
    Ast.AstFromVector l -> astSumOfList $ V.toList l
    Ast.AstReplicate k v -> v * astReplicate0N (shapeAst v) (fromIntegral k)
    Ast.AstReverse v -> Ast.AstSum v
    AstConst t -> AstConst $ tsumR t
    Ast.AstConstant v -> Ast.AstConstant $ astSum v
    _ -> Ast.AstSum t0

astSumS :: forall n sh r s. (KnownNat n, Sh.Shape sh, GoodScalar r, AstSpan s)
        => AstShaped s r (n ': sh) -> AstShaped s r sh
astSumS t0 = case sameNat (Proxy @n) (Proxy @0) of
 Just Refl -> 0
 _ -> case sameNat (Proxy @n) (Proxy @1) of
  Just Refl -> astReshapeS t0
  _ -> case t0 of
    -- Ast.AstLetS var u v -> astLetS var u (astSumS v)
    Ast.AstLetADShareS l v -> Ast.AstLetADShareS l (astSumS v)
    Ast.AstScatterS @sh2 @p v (vars, _ ::$ ix) ->
      gcastWith (unsafeCoerce Refl
                 :: Sh.Drop p (n : sh) :~: Sh.Drop (p - 1) sh) $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Drop 1 (Sh.Take p (n : sh)) :~: Sh.Take (p - 1) sh) $
      astScatterS @sh2 @(p - 1) @sh v (vars, ix)
    Ast.AstFromListS l -> astSumOfListS l
    Ast.AstFromVectorS l -> astSumOfListS $ V.toList l
    Ast.AstReplicateS @k v -> v * astReplicate0NS (valueOf @k)
    Ast.AstReverseS v -> Ast.AstSumS v
    AstConstS t -> AstConstS $ tsumS t
    Ast.AstConstantS v -> Ast.AstConstantS $ astSumS v
    _ -> Ast.AstSumS t0

-- TODO: fuse scatters, scatter and sum, perhaps more (fromList?)
astScatter :: forall m n p s r.
              (GoodScalar r, KnownNat m, KnownNat n, KnownNat p, AstSpan s)
           => ShapeInt (p + n) -> AstRanked s r (m + n)
           -> (AstVarList m, AstIndex p)
           -> AstRanked s r (p + n)
astScatter _sh v (ZR, ZIR) = v
astScatter sh v (AstVarName varId ::: vars, ix) | not $ varId `varInIndex` ix =
  astScatter sh (astSum v) (vars, ix)
-- astScatter sh v (ZR, ix) = update (rzero sh 0) ix v
astScatter sh (Ast.AstConstant v) (vars, ix) =
  Ast.AstConstant $ astScatter sh v (vars, ix)
astScatter sh (Ast.AstLetADShare l v) (vars, ix) =
  Ast.AstLetADShare l $ astScatter sh v (vars, ix)
astScatter sh v (vars, ix) = Ast.AstScatter sh v (vars, ix)

astScatterS :: forall sh2 p sh s r.
               ( Sh.Shape sh2, Sh.Shape sh
               , Sh.Shape (Sh.Take p sh), Sh.Shape (Sh.Drop p sh)
               , Sh.Shape (sh2 Sh.++ Sh.Drop p sh), GoodScalar r, AstSpan s )
            => AstShaped s r (sh2 Sh.++ Sh.Drop p sh)
            -> (AstVarListS sh2, AstIndexS (Sh.Take p sh))
            -> AstShaped s r sh
astScatterS v (ZS, ZS) =
  gcastWith (unsafeCoerce Refl
             :: Sh.Take p sh Sh.++ Sh.Drop p sh :~: sh)
  v
astScatterS v (AstVarName varId ::$ (vars :: AstVarListS sh3), ix)
  | not $ varId `varInIndexS` ix =
    Sh.withShapeP (Sh.shapeT @sh3
                   ++ (Sh.shapeT @(Sh.Drop p sh))) $ \(Proxy @sh4) ->
      gcastWith (unsafeCoerce Refl :: sh3 Sh.++ Sh.Drop p sh :~: sh4) $
      astScatterS @sh3 @p @sh (astSumS v) (vars, ix)
-- astScatterS v (ZR, ix) = update (rzero sh 0) ix v
astScatterS (Ast.AstConstantS v) (vars, ix) =
  Ast.AstConstantS $ astScatterS v (vars, ix)
astScatterS (Ast.AstLetADShareS l v) (vars, ix) =
  Ast.AstLetADShareS l $ astScatterS v (vars, ix)
astScatterS v (vars, ix) = Ast.AstScatterS v (vars, ix)

astFromList :: forall s r n. (KnownNat n, GoodScalar r, AstSpan s)
            => [AstRanked s r n] -> AstRanked s r (1 + n)
astFromList [a] = astReplicate 1 a
astFromList l | Just Refl <- sameAstSpan @s @PrimalSpan =
  let unConst :: AstRanked PrimalSpan r n -> Maybe (OR.Array n r)
      unConst (AstConst t) = Just t
      unConst _ = Nothing
  in case mapM unConst l of
    Just l3 -> AstConst $ tfromListR l3
    Nothing -> Ast.AstFromList l
astFromList l | Just Refl <- sameAstSpan @s @FullSpan =
  let unConstant :: AstRanked FullSpan r n -> Maybe (AstRanked PrimalSpan r n)
      unConstant (Ast.AstConstant t) = Just t
      unConstant _ = Nothing
  in case mapM unConstant l of
    Just [] -> Ast.AstFromList []
    Just l2 -> Ast.AstConstant $ astFromList l2
    Nothing -> Ast.AstFromList l
astFromList l = Ast.AstFromList l

astFromListS :: forall s r n sh.
                (KnownNat n, Sh.Shape sh, GoodScalar r, AstSpan s)
             => [AstShaped s r sh] -> AstShaped s r (n ': sh)
astFromListS [a] = astReplicateS a
astFromListS l | Just Refl <- sameAstSpan @s @PrimalSpan =
  let unConst :: AstShaped PrimalSpan r sh -> Maybe (OS.Array sh r)
      unConst (AstConstS t) = Just t
      unConst _ = Nothing
  in case mapM unConst l of
    Just l3 -> AstConstS $ tfromListS l3
    Nothing -> Ast.AstFromListS l
astFromListS l | Just Refl <- sameAstSpan @s @FullSpan =
  let unConstant :: AstShaped FullSpan r sh -> Maybe (AstShaped PrimalSpan r sh)
      unConstant (Ast.AstConstantS t) = Just t
      unConstant _ = Nothing
  in case mapM unConstant l of
    Just [] -> Ast.AstFromListS []
    Just l2 -> Ast.AstConstantS $ astFromListS l2
    Nothing -> Ast.AstFromListS l
astFromListS l = Ast.AstFromListS l

astFromVector :: forall s r n. (KnownNat n, GoodScalar r, AstSpan s)
              => Data.Vector.Vector (AstRanked s r n) -> AstRanked s r (1 + n)
astFromVector v | V.length v == 1 = astReplicate 1 (v V.! 0)
astFromVector l | Just Refl <- sameAstSpan @s @PrimalSpan =
  let unConst :: AstRanked PrimalSpan r n -> Maybe (OR.Array n r)
      unConst (AstConst t) = Just t
      unConst _ = Nothing
  in case V.mapM unConst l of
    Just l3 -> AstConst $ tfromVectorR l3
    Nothing -> Ast.AstFromVector l
astFromVector l | Just Refl <- sameAstSpan @s @FullSpan =
  let unConstant :: AstRanked FullSpan r n -> Maybe (AstRanked PrimalSpan r n)
      unConstant (Ast.AstConstant t) = Just t
      unConstant _ = Nothing
  in case V.mapM unConstant l of
    Just l2 | V.null l2 -> Ast.AstFromVector V.empty
    Just l2 -> Ast.AstConstant $ astFromVector l2
    Nothing -> Ast.AstFromVector l
astFromVector l = Ast.AstFromVector l

astFromVectorS :: forall s r n sh.
                  (KnownNat n, Sh.Shape sh, GoodScalar r, AstSpan s)
               => Data.Vector.Vector (AstShaped s r sh)
               -> AstShaped s r (n ': sh)
astFromVectorS v | V.length v == 1 = astReplicateS (v V.! 0)
astFromVectorS l | Just Refl <- sameAstSpan @s @PrimalSpan =
  let unConst :: AstShaped PrimalSpan r sh -> Maybe (OS.Array sh r)
      unConst (AstConstS t) = Just t
      unConst _ = Nothing
  in case V.mapM unConst l of
    Just l3 -> AstConstS $ tfromVectorS l3
    Nothing -> Ast.AstFromVectorS l
astFromVectorS l | Just Refl <- sameAstSpan @s @FullSpan =
  let unConstant :: AstShaped FullSpan r sh -> Maybe (AstShaped PrimalSpan r sh)
      unConstant (Ast.AstConstantS t) = Just t
      unConstant _ = Nothing
  in case V.mapM unConstant l of
    Just l2 | V.null l2 -> Ast.AstFromVectorS V.empty
    Just l2 -> Ast.AstConstantS $ astFromVectorS l2
    Nothing -> Ast.AstFromVectorS l
astFromVectorS l = Ast.AstFromVectorS l

astReplicate :: (KnownNat n, GoodScalar r, AstSpan s)
             => Int -> AstRanked s r n -> AstRanked s r (1 + n)
astReplicate k = \case
  Ast.AstLetADShare l v -> Ast.AstLetADShare l $ astReplicate k v
{- TODO: these may be counterproductive with many gathers and their fusion
         though these let transpose cancel out with each other sometimes
         (instead we should try to cancel out inside replicate and only move
          if they don't) -}
  Ast.AstTranspose perm v ->
    astTranspose (0 : map succ perm) $ astReplicate k v
{- see the previous comment
  Ast.AstReshape sh v ->
    AstReshape (k :$: sh) $ astReplicate k v
-}
-- This allocates a big tensor too early, while it's still possible
-- a projection reduces this away. The cost to AD should not be too high.
-- This would also hide AstReplicate from hacks that recover tmatmul2, etc.
--  AstConst t -> AstConst $ treplicateR k t
  Ast.AstConstant v -> Ast.AstConstant $ astReplicate k v
  v -> Ast.AstReplicate k v

astReplicateS :: forall n sh s r.
                 (KnownNat n, Sh.Shape sh, GoodScalar r, AstSpan s)
              => AstShaped s r sh -> AstShaped s r (n ': sh)
astReplicateS = \case
  Ast.AstLetADShareS l v -> Ast.AstLetADShareS l $ astReplicateS v
  Ast.AstTransposeS @perm @sh1 v ->
    let zsuccPerm = 0 : map succ (Sh.shapeT @perm)
    in Sh.withShapeP zsuccPerm $ \(Proxy @zsuccP) ->
      gcastWith (unsafeCoerce Refl :: 0 ': MapSucc perm :~: zsuccP) $
        -- this one is needed for GHC >= 9.8 due to #23763
      gcastWith (unsafeCoerce Refl
                 :: Sh.Permute zsuccP (n : sh1) :~: n : sh) $
      gcastWith (unsafeCoerce Refl :: Sh.Rank zsuccP :~: 1 + Sh.Rank perm) $
      trustMeThisIsAPermutation @zsuccP $
      astTransposeS @zsuccP $ astReplicateS @n v
  Ast.AstConstantS v -> Ast.AstConstantS $ astReplicateS v
  v -> Ast.AstReplicateS v

astReplicateN :: forall n p s r.
                 (KnownNat n, KnownNat p, GoodScalar r, AstSpan s)
              => ShapeInt (n + p) -> AstRanked s r p -> AstRanked s r (n + p)
astReplicateN sh v =
  let go :: KnownNat n'
         => ShapeInt n' -> AstRanked s r (n' + p)
      go ZSR = v
      go (k :$: sh2) = astReplicate k $ go sh2
  in go (takeShape sh)

astReplicateNS :: forall shn shp s r.
                  (Sh.Shape shn, Sh.Shape shp, GoodScalar r, AstSpan s)
               => AstShaped s r shp -> AstShaped s r (shn Sh.++ shp)
astReplicateNS v =
  let go :: ShapeSh shn' -> AstShaped s r (shn' Sh.++ shp)
      go ZS = v
      go ((::$) @k @shn2 _ shn2) =
        Sh.withShapeP (Sh.shapeT @shn2 ++ Sh.shapeT @shp) $ \(Proxy @sh) ->
          gcastWith (unsafeCoerce Refl :: sh :~: shn2 Sh.++ shp) $
          astReplicateS @k $ go shn2
  in go (ShapedList.shapeSh @shn)

astReplicate0N :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
               => ShapeInt n -> AstRanked s r 0 -> AstRanked s r n
astReplicate0N sh =
  let go :: KnownNat n'
         => ShapeInt n' -> AstRanked s r 0 -> AstRanked s r n'
      go ZSR v = v
      go (k :$: sh') v = astReplicate k $ go sh' v
  in go sh

astReplicate0NS :: forall shn s r. (Sh.Shape shn, GoodScalar r, AstSpan s)
                => AstShaped s r '[] -> AstShaped s r shn
astReplicate0NS =
  let go :: ShapedList sh' Int -> AstShaped s r '[] -> AstShaped s r sh'
      go ZS v = v
      go (_ ::$ sh') v = astReplicateS $ go sh' v
  in go (ShapedList.shapeSh @shn)

astAppend :: (KnownNat n, GoodScalar r, AstSpan s)
          => AstRanked s r (1 + n) -> AstRanked s r (1 + n)
          -> AstRanked s r (1 + n)
astAppend (AstConst u) (AstConst v) = AstConst $ tappendR u v
astAppend (Ast.AstConstant u) (Ast.AstConstant v) =
  Ast.AstConstant $ astAppend u v
astAppend (Ast.AstLetADShare l u) v =
  Ast.AstLetADShare l $ astAppend u v
astAppend u (Ast.AstLetADShare l v) =
  Ast.AstLetADShare l $ astAppend u v
astAppend (Ast.AstFromList l1) (Ast.AstFromList l2) = astFromList $ l1 ++ l2
astAppend (Ast.AstFromList l1) (Ast.AstFromVector l2) =
  astFromList $ l1 ++ V.toList l2
astAppend (Ast.AstFromVector l1) (Ast.AstFromList l2) =
  astFromList $ V.toList l1 ++ l2
astAppend (Ast.AstFromVector l1) (Ast.AstFromVector l2) =
  astFromVector $ l1 V.++ l2
astAppend u v = Ast.AstAppend u v

astAppendS :: (KnownNat m, KnownNat n, Sh.Shape sh, GoodScalar r, AstSpan s)
           => AstShaped s r (m ': sh) -> AstShaped s r (n ': sh)
           -> AstShaped s r ((m + n) ': sh)
astAppendS (AstConstS u) (AstConstS v) = AstConstS $ tappendS u v
astAppendS (Ast.AstConstantS u) (Ast.AstConstantS v) =
  Ast.AstConstantS $ astAppendS u v
astAppendS (Ast.AstLetADShareS l u) v =
  Ast.AstLetADShareS l $ astAppendS u v
astAppendS u (Ast.AstLetADShareS l v) =
  Ast.AstLetADShareS l $ astAppendS u v
astAppendS (Ast.AstFromListS l1) (Ast.AstFromListS l2) = astFromListS $ l1 ++ l2
astAppendS (Ast.AstFromListS l1) (Ast.AstFromVectorS l2) =
  astFromListS $ l1 ++ V.toList l2
astAppendS (Ast.AstFromVectorS l1) (Ast.AstFromListS l2) =
  astFromListS $ V.toList l1 ++ l2
astAppendS (Ast.AstFromVectorS l1) (Ast.AstFromVectorS l2) =
  astFromVectorS $ l1 V.++ l2
astAppendS u v = Ast.AstAppendS u v

astSlice :: forall k s r. (KnownNat k, GoodScalar r, AstSpan s)
         => Int -> Int -> AstRanked s r (1 + k) -> AstRanked s r (1 + k)
astSlice i n (AstConst t) = AstConst $ tsliceR i n t
astSlice i n (Ast.AstConstant v) = Ast.AstConstant $ astSlice i n v
astSlice i n (Ast.AstLetADShare l v) = Ast.AstLetADShare l $ astSlice i n v
astSlice 0 n v | n == lengthAst v = v
astSlice i n (Ast.AstFromList l) = astFromList $ take n (drop i l)
astSlice i n (Ast.AstFromVector l) = astFromVector $ V.take n (V.drop i l)
astSlice _i n (Ast.AstReplicate _n2 v) = astReplicate n v
astSlice i n w@(Ast.AstAppend (u :: AstRanked s r (1 + k))
                              (v :: AstRanked s r (1 + k))) =
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
astSlice i n (Ast.AstGather (_ :$: sh') v (var ::: vars, ix)) =
  let ivar = AstIntVar var + fromIntegral i
      ix2 = substituteAstIndex  -- cheap subst, because ivar is tiny
              (SubstitutionPayloadRanked @PrimalSpan @Int64 ivar)
              var ix
  in astGatherR (n :$: sh') v (var ::: vars, ix2)
astSlice i n v = Ast.AstSlice i n v

astSliceS :: forall i n k sh s r.
             ( KnownNat i, KnownNat n, KnownNat k, Sh.Shape sh, GoodScalar r
             , AstSpan s )
          => AstShaped s r (i + n + k ': sh) -> AstShaped s r (n ': sh)
astSliceS (AstConstS t) = AstConstS $ tsliceS @i @n t
astSliceS (Ast.AstConstantS v) = Ast.AstConstantS $ astSliceS @i @n v
astSliceS (Ast.AstLetADShareS l v) = Ast.AstLetADShareS l $ astSliceS @i @n v
astSliceS v | Just Refl <- sameNat (Proxy @i) (Proxy @0)
            , Just Refl <- sameNat (Proxy @k) (Proxy @0) = v
astSliceS (Ast.AstFromListS l) =
  astFromListS $ take (valueOf @n) (drop (valueOf @i) l)
astSliceS (Ast.AstFromVectorS l) =
  astFromVectorS $ V.take (valueOf @n) (V.drop (valueOf @i) l)
astSliceS (Ast.AstReplicateS v) = astReplicateS @n v
astSliceS w@(Ast.AstAppendS (u :: AstShaped s r (ulen : sh))
                            (v :: AstShaped s r (vlen : sh))) =
  case cmpNat (Proxy @(i + n)) (Proxy @ulen) of
    LTI -> astSliceS @i @n @(ulen - (i + n)) u
    EQI -> astSliceS @i @n @0 u
    GTI ->
      gcastWith (unsafeCoerce Refl :: vlen :~: i - ulen + n + k) $
      case cmpNat (Proxy @ulen) (Proxy @i) of
        LTI -> astSliceS @(i - ulen) @n @k v
        EQI -> astSliceS @0 @n @k v
        GTI -> Ast.AstSliceS @i w -- cheap iff fits in one
astSliceS (Ast.AstGatherS v (var ::$ vars, ix)) =
  let ivar = AstIntVar var + valueOf @i
      ix2 = substituteAstIndexS  -- cheap subst, because ivar is tiny
              (SubstitutionPayloadRanked @PrimalSpan @Int64 ivar)
              var ix
  in astGatherS v (var ::$ vars, ix2)
astSliceS v = Ast.AstSliceS @i v

astReverse :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
           => AstRanked s r (1 + n) -> AstRanked s r (1 + n)
astReverse (AstConst t) = AstConst $ treverseR t
astReverse (Ast.AstConstant v) = Ast.AstConstant $ astReverse v
astReverse (Ast.AstLetADShare l v) = Ast.AstLetADShare l $ astReverse v
astReverse (Ast.AstFromList l) = Ast.AstFromList $ reverse l
astReverse (Ast.AstFromVector l) = Ast.AstFromVector $ V.reverse l
astReverse (Ast.AstReplicate k v) = Ast.AstReplicate k v
astReverse (Ast.AstReverse v) = v
astReverse (Ast.AstGather sh@(k :$: _) v (var ::: vars, ix)) =
  let ivar = fromIntegral k - AstIntVar var
      ix2 = substituteAstIndex  -- cheap subst, because ivar is tiny
              (SubstitutionPayloadRanked @PrimalSpan @Int64 ivar)
              var ix
  in astGatherR sh v (var ::: vars, ix2)
astReverse v = Ast.AstReverse v

astReverseS :: forall n sh s r. (KnownNat n, Sh.Shape sh, GoodScalar r)
            => AstShaped s r (n ': sh) -> AstShaped s r (n ': sh)
astReverseS (AstConstS t) = AstConstS $ treverseS t
astReverseS (Ast.AstConstantS v) = Ast.AstConstantS $ astReverseS v
astReverseS (Ast.AstLetADShareS l v) = Ast.AstLetADShareS l $ astReverseS v
astReverseS (Ast.AstFromListS l) = Ast.AstFromListS $ reverse l
astReverseS (Ast.AstFromVectorS l) = Ast.AstFromVectorS $ V.reverse l
astReverseS (Ast.AstReplicateS v) = Ast.AstReplicateS v
astReverseS (Ast.AstReverseS v) = v
astReverseS (Ast.AstGatherS v ((::$) @k var vars, ix)) =
  let ivar = valueOf @k - AstIntVar var
      ix2 = substituteAstIndexS  -- cheap subst, because ivar is tiny
              (SubstitutionPayloadRanked @PrimalSpan @Int64 ivar)
              var ix
  in astGatherS v (var ::$ vars, ix2)
astReverseS v = Ast.AstReverseS v

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astTransposeAsGather needs to be called in addition
-- if full simplification is required.
astTranspose :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
             => Permutation -> AstRanked s r n -> AstRanked s r n
astTranspose perm = \case
  t | null perm -> t
  Ast.AstLet var u v -> astLet var u (astTranspose perm v)
  AstN1 opCode u | not (isVar u) -> AstN1 opCode (astTranspose perm u)
  AstN2 opCode u@Ast.AstTranspose{} v ->
    AstN2 opCode (astTranspose perm u) (astTranspose perm v)
  AstN2 opCode u@(Ast.AstConstant Ast.AstTranspose{}) v ->
    AstN2 opCode (astTranspose perm u) (astTranspose perm v)
  AstN2 opCode u v@Ast.AstTranspose{} ->
    AstN2 opCode (astTranspose perm u) (astTranspose perm v)
  AstN2 opCode u v@(Ast.AstConstant Ast.AstTranspose{}) ->
    AstN2 opCode (astTranspose perm u) (astTranspose perm v)
  Ast.AstR1 opCode u | not (isVar u) -> Ast.AstR1 opCode (astTranspose perm u)
  Ast.AstR2 opCode u@Ast.AstTranspose{} v ->
    Ast.AstR2 opCode (astTranspose perm u) (astTranspose perm v)
  Ast.AstR2 opCode u@(Ast.AstConstant Ast.AstTranspose{}) v ->
    Ast.AstR2 opCode (astTranspose perm u) (astTranspose perm v)
  Ast.AstR2 opCode u v@Ast.AstTranspose{} ->
    Ast.AstR2 opCode (astTranspose perm u) (astTranspose perm v)
  Ast.AstR2 opCode u v@(Ast.AstConstant Ast.AstTranspose{}) ->
    Ast.AstR2 opCode (astTranspose perm u) (astTranspose perm v)
  Ast.AstSum v -> astSum $ astTranspose (0 : map succ perm) v
  Ast.AstScatter @_ @_ @p sh v (vars, ix) | length perm <= valueOf @p ->
    -- TODO: should the below be backpermute or permute?
    astScatter (backpermutePrefixShape perm sh) v
               (vars, backpermutePrefixIndex perm ix)
  Ast.AstTranspose perm2 t ->
    let perm2Matched =
          perm2
          ++ take (length perm - length perm2) (drop (length perm2) [0 ..])
        perm3 = simplifyPermutation $ backpermutePrefixList perm perm2Matched
    in astTranspose perm3 t
      -- this rule can be disabled to test fusion of gathers
  -- Note that the following would be wrong, because transpose really
  -- changes the linearisation order, while reshape only modifies indexing:
  -- (perm, AstReshape sh v) -> astReshape (backpermutePrefixShape perm sh) v
  Ast.AstGather @m sh v (vars, ix) | length perm <= valueOf @m ->
    -- TODO: should the below be backpermute or permute?
    astGatherR (backpermutePrefixShape perm sh) v
               (backpermutePrefixSized perm vars, ix)
  AstConst t -> AstConst $ ttransposeR perm t
  Ast.AstConstant v -> Ast.AstConstant $ astTranspose perm v
  Ast.AstLetADShare l v -> Ast.AstLetADShare l $ astTranspose perm v
  u -> Ast.AstTranspose perm u

astTransposeS :: forall perm sh s r.
                 ( OS.Permutation perm, Sh.Shape perm, Sh.Shape sh
                 , KnownNat (Sh.Rank sh), Sh.Rank perm <= Sh.Rank sh
                 , GoodScalar r, AstSpan s )
              => AstShaped s r sh -> AstShaped s r (Sh.Permute perm sh)
astTransposeS = \case
  t | Just Refl <- sameShape @perm @'[] -> t
  Ast.AstLetS var u v ->
    Sh.withShapeP (backpermutePrefixList (Sh.shapeT @perm)
                                         (Sh.shapeT @sh)) $ \(Proxy @shp) ->
      gcastWith (unsafeCoerce Refl :: Sh.Permute perm sh :~: shp) $
      astLetS var u (astTransposeS @perm v)
  AstN1S opCode u | not (isVarS u) -> AstN1S opCode (astTransposeS @perm u)
  AstN2S opCode u@Ast.AstTransposeS{} v ->
    AstN2S opCode (astTransposeS @perm u) (astTransposeS @perm v)
  AstN2S opCode u@(Ast.AstConstantS Ast.AstTransposeS{}) v ->
    AstN2S opCode (astTransposeS @perm u) (astTransposeS @perm v)
  AstN2S opCode u v@Ast.AstTransposeS{} ->
    AstN2S opCode (astTransposeS @perm u) (astTransposeS @perm v)
  AstN2S opCode u v@(Ast.AstConstantS Ast.AstTransposeS{}) ->
    AstN2S opCode (astTransposeS @perm u) (astTransposeS @perm v)
  Ast.AstR1S opCode u | not (isVarS u) ->
    Ast.AstR1S opCode (astTransposeS @perm u)
  Ast.AstR2S opCode u@Ast.AstTransposeS{} v ->
    Ast.AstR2S opCode (astTransposeS @perm u) (astTransposeS @perm v)
  Ast.AstR2S opCode u@(Ast.AstConstantS Ast.AstTransposeS{}) v ->
    Ast.AstR2S opCode (astTransposeS @perm u) (astTransposeS @perm v)
  Ast.AstR2S opCode u v@Ast.AstTransposeS{} ->
    Ast.AstR2S opCode (astTransposeS @perm u) (astTransposeS @perm v)
  Ast.AstR2S opCode u v@(Ast.AstConstantS Ast.AstTransposeS{}) ->
    Ast.AstR2S opCode (astTransposeS @perm u) (astTransposeS @perm v)
  Ast.AstSumS @n @sh1 v ->
    let zsuccPerm = 0 : map succ (Sh.shapeT @perm)
    in Sh.withShapeP zsuccPerm $ \(Proxy @zsuccP) ->
      gcastWith (unsafeCoerce Refl :: 0 ': MapSucc perm :~: zsuccP) $
      Sh.withShapeP (backpermutePrefixList (Sh.shapeT @perm)
                                           (Sh.shapeT @sh)) $ \(Proxy @shp) ->
        gcastWith (unsafeCoerce Refl :: Sh.Permute perm sh :~: shp) $
        gcastWith (unsafeCoerce Refl :: Sh.Rank zsuccP :~: 1 + Sh.Rank perm) $
        gcastWith (unsafeCoerce Refl
                   :: Sh.Permute zsuccP (n : sh) :~: n : Sh.Permute perm sh) $
        trustMeThisIsAPermutation @zsuccP $
        astSumS $ astTransposeS @zsuccP v
  Ast.AstScatterS @sh2 @p v (vars, ix)
    -- TODO: should the below be backpermute or permute?
    | length (Sh.shapeT @perm) <= length (Sh.shapeT @(Sh.Take p sh)) ->
      Sh.withShapeP
        (backpermutePrefixList (Sh.shapeT @perm)
                               (Sh.shapeT @sh)) $ \(Proxy @shPerm) ->
          gcastWith (unsafeCoerce Refl :: Sh.Permute perm sh :~: shPerm) $
        Sh.withShapeP (take (length ix)
                       $ Sh.shapeT @shPerm) $ \(Proxy @shpPerm) ->
          gcastWith (unsafeCoerce Refl :: Sh.Take p shPerm :~: shpPerm) $
          gcastWith (unsafeCoerce Refl
                     :: Sh.Permute perm (Sh.Take p sh) :~: shpPerm) $
          let ix2 :: AstIndexS (Sh.Take p shPerm) =
                ShapedList.backpermutePrefixShaped @perm ix
          in gcastWith (unsafeCoerce Refl
                        :: Sh.Drop p shPerm :~: Sh.Drop p sh) $
             astScatterS @sh2 @p @shPerm v (vars, ix2)
  Ast.AstTransposeS @perm2 @sh2 t ->  -- TODO: try to perform at type level
    let permV = Sh.shapeT @perm
        perm2V = Sh.shapeT @perm2
        perm2Matched =
          perm2V
          ++ take (length permV - length perm2V) (drop (length perm2V) [0 ..])
        perm3V = simplifyPermutation $ backpermutePrefixList permV perm2Matched
    in Sh.withShapeP perm3V $ \(Proxy @perm3) ->
      trustMeThisIsAPermutation @perm3 $
      gcastWith (unsafeCoerce Refl
                 :: Compare (OS.Rank perm3) (OS.Rank sh2) :~: LT) $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Permute perm3 sh2 :~: Sh.Permute perm sh) $
      astTransposeS @perm3 t
  Ast.AstGatherS @sh2 @p @sh3 v (vars, ix)
    -- TODO: should the below be backpermute or permute?
    | length (Sh.shapeT @perm) <= length (Sh.shapeT @(Sh.Take p sh3)) ->
      Sh.withShapeP (backpermutePrefixList
                       (Sh.shapeT @perm)
                       (Sh.shapeT @sh2)) $ \(Proxy @shmPerm) ->
        gcastWith (unsafeCoerce Refl
                   :: Sh.Permute perm sh2 :~: shmPerm) $
        let vars2 :: AstVarListS shmPerm =
              ShapedList.backpermutePrefixShaped @perm vars
        in gcastWith (unsafeCoerce Refl
                      :: Sh.Permute perm sh2 Sh.++ Sh.Drop p sh3
                         :~: Sh.Permute perm sh) $
           astGatherS @(Sh.Permute perm sh2) @p @sh3 v (vars2, ix)
  AstConstS t -> AstConstS $ ttransposeS @perm t
  Ast.AstConstantS v -> Ast.AstConstantS $ astTransposeS @perm v
  Ast.AstLetADShareS l v -> Ast.AstLetADShareS l $ astTransposeS @perm v
  u -> Ast.AstTransposeS @perm u  -- TODO

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astReshapeAsGather needs to be called in addition
-- if full simplification is required.
astReshape :: forall p m s r. (KnownNat p, KnownNat m, GoodScalar r, AstSpan s)
           => ShapeInt m -> AstRanked s r p -> AstRanked s r m
astReshape shOut = \case
  Ast.AstLet var u v -> astLet var u (astReshape shOut v)
  AstN1 opCode u | not (isVar u) -> AstN1 opCode (astReshape shOut u)
  AstN2 opCode (Ast.AstReshape _ u) v ->
    AstN2 opCode (astReshape shOut u) (astReshape shOut v)
  AstN2 opCode (Ast.AstConstant (Ast.AstReshape _ u)) v ->
    AstN2 opCode (astReshape shOut (Ast.AstConstant u)) (astReshape shOut v)
  AstN2 opCode u (Ast.AstReshape _ v) ->
    AstN2 opCode (astReshape shOut u) (astReshape shOut v)
  AstN2 opCode u (Ast.AstConstant (Ast.AstReshape _ v)) ->
    AstN2 opCode (astReshape shOut u) (astReshape shOut (Ast.AstConstant v))
  Ast.AstR1 opCode u | not (isVar u) -> Ast.AstR1 opCode (astReshape shOut u)
  Ast.AstR2 opCode (Ast.AstReshape _ u) v ->
    Ast.AstR2 opCode (astReshape shOut u) (astReshape shOut v)
  Ast.AstR2 opCode (Ast.AstConstant (Ast.AstReshape _ u)) v ->
    Ast.AstR2 opCode (astReshape shOut (Ast.AstConstant u)) (astReshape shOut v)
  Ast.AstR2 opCode u (Ast.AstReshape _ v) ->
    Ast.AstR2 opCode (astReshape shOut u) (astReshape shOut v)
  Ast.AstR2 opCode u (Ast.AstConstant (Ast.AstReshape _ v)) ->
    Ast.AstR2 opCode (astReshape shOut u) (astReshape shOut (Ast.AstConstant v))
  Ast.AstFromList [x] -> astReshape shOut x
  Ast.AstFromVector l | [x] <- V.toList l -> astReshape shOut x
  Ast.AstReplicate 1 x -> astReshape shOut x
  Ast.AstReshape _ v -> astReshape shOut v
  AstConst t -> AstConst $ OR.reshape (shapeToList shOut) t
  Ast.AstConstant v -> Ast.AstConstant $ astReshape shOut v
  Ast.AstLetADShare l v -> Ast.AstLetADShare l $ astReshape shOut v
  v -> let shIn = shapeAst v
       in case sameNat (Proxy @p) (Proxy @m) of
         Just Refl -> if shIn == shOut
                      then v
                      else Ast.AstReshape shOut v
         _ -> Ast.AstReshape shOut v

astReshapeS :: forall sh sh2 r s.
               ( Sh.Shape sh, Sh.Shape sh2, Sh.Size sh ~ Sh.Size sh2
               , GoodScalar r, AstSpan s )
            => AstShaped s r sh -> AstShaped s r sh2
astReshapeS = \case
  Ast.AstLetS var u v -> astLetS var u (astReshapeS @_ @sh2 v)
  AstN1S opCode u | not (isVarS u) -> AstN1S opCode (astReshapeS @_ @sh2 u)
  AstN2S opCode (Ast.AstReshapeS u) v ->
    AstN2S opCode (astReshapeS @_ @sh2 u) (astReshapeS @_ @sh2 v)
  AstN2S opCode (Ast.AstConstantS (Ast.AstReshapeS u)) v ->
    AstN2S opCode (astReshapeS @_ @sh2 (Ast.AstConstantS u))
                  (astReshapeS @_ @sh2 v)
  AstN2S opCode u (Ast.AstReshapeS v) ->
    AstN2S opCode (astReshapeS @_ @sh2 u) (astReshapeS @_ @sh2 v)
  AstN2S opCode u (Ast.AstConstantS (Ast.AstReshapeS v)) ->
    AstN2S opCode (astReshapeS @_ @sh2 u)
                  (astReshapeS @_ @sh2 (Ast.AstConstantS v))
  Ast.AstR1S opCode u | not (isVarS u) ->
    Ast.AstR1S opCode (astReshapeS @_ @sh2 u)
  Ast.AstR2S opCode (Ast.AstReshapeS u) v ->
    Ast.AstR2S opCode (astReshapeS @_ @sh2 u) (astReshapeS @_ @sh2 v)
  Ast.AstR2S opCode (Ast.AstConstantS (Ast.AstReshapeS u)) v ->
    Ast.AstR2S opCode (astReshapeS @_ @sh2 (Ast.AstConstantS u))
                      (astReshapeS @_ @sh2 v)
  Ast.AstR2S opCode u (Ast.AstReshapeS v) ->
    Ast.AstR2S opCode (astReshapeS @_ @sh2 u) (astReshapeS @_ @sh2 v)
  Ast.AstR2S opCode u (Ast.AstConstantS (Ast.AstReshapeS v)) ->
    Ast.AstR2S opCode (astReshapeS @_ @sh2 u)
                      (astReshapeS @_ @sh2 (Ast.AstConstantS v))
  Ast.AstFromListS @n l | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
    astReshapeS $ l !! 0
  Ast.AstFromVectorS @n l | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
    astReshapeS $ l V.! 0
  Ast.AstReplicateS @n x | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
    astReshapeS x
  Ast.AstReshapeS v -> astReshapeS @_ @sh2 v
  AstConstS t -> AstConstS $ OS.reshape t
  Ast.AstConstantS v -> Ast.AstConstantS $ astReshapeS v
  Ast.AstLetADShareS l v -> Ast.AstLetADShareS l $ astReshapeS v
  v -> case sameShape @sh @sh2 of
         Just Refl -> v
         _ -> Ast.AstReshapeS v

astCast :: (KnownNat n, GoodScalar r1, GoodScalar r2, RealFrac r1, RealFrac r2)
        => AstRanked s r1 n -> AstRanked s r2 n
astCast (AstConst t) = AstConst $ tcastR t
astCast (Ast.AstConstant v) = Ast.AstConstant $ astCast v
astCast (Ast.AstLetADShare l v) = Ast.AstLetADShare l $ astCast v
astCast (Ast.AstCast v) = astCast v
astCast (Ast.AstFromIntegral v) = astFromIntegral v
astCast v = Ast.AstCast v

astCastS :: ( Sh.Shape sh, GoodScalar r1, GoodScalar r2, RealFrac r1
            , RealFrac r2 )
         => AstShaped s r1 sh -> AstShaped s r2 sh
astCastS (AstConstS t) = AstConstS $ tcastS t
astCastS (Ast.AstConstantS v) = Ast.AstConstantS $ astCastS v
astCastS (Ast.AstLetADShareS l v) = Ast.AstLetADShareS l $ astCastS v
astCastS (Ast.AstCastS v) = astCastS v
astCastS (Ast.AstFromIntegralS v) = astFromIntegralS v
astCastS v = Ast.AstCastS v

astFromIntegral :: (KnownNat n, GoodScalar r1, GoodScalar r2, Integral r1)
                => AstRanked PrimalSpan r1 n -> AstRanked PrimalSpan r2 n
astFromIntegral (AstConst t) = AstConst $ tfromIntegralR t
astFromIntegral (Ast.AstLetADShare l v) =
  Ast.AstLetADShare l $ astFromIntegral v
astFromIntegral (Ast.AstFromIntegral v) = astFromIntegral v
astFromIntegral v = Ast.AstFromIntegral v

astFromIntegralS :: (Sh.Shape sh, GoodScalar r1, GoodScalar r2, Integral r1)
                 => AstShaped PrimalSpan r1 sh -> AstShaped PrimalSpan r2 sh
astFromIntegralS (AstConstS t) = AstConstS $ tfromIntegralS t
astFromIntegralS (Ast.AstLetADShareS l v) =
  Ast.AstLetADShareS l $ astFromIntegralS v
astFromIntegralS (Ast.AstFromIntegralS v) = astFromIntegralS v
astFromIntegralS v = Ast.AstFromIntegralS v

astRFromS :: Sh.Shape sh
          => AstShaped s r sh -> AstRanked s r (Sh.Rank sh)
astRFromS (AstConstS t) = AstConst $ Data.Array.Convert.convert t
astRFromS (Ast.AstConstantS v) = Ast.AstConstant $ astRFromS v
astRFromS (Ast.AstLetADShareS l v) = Ast.AstLetADShare l $ astRFromS v
astRFromS (Ast.AstSFromR v) = v  -- no information lost, so no checks
astRFromS v = Ast.AstRFromS v

astSFromR :: forall sh s r. (Sh.Shape sh, KnownNat (Sh.Rank sh))
          => AstRanked s r (Sh.Rank sh) -> AstShaped s r sh
astSFromR (AstConst t) = AstConstS $ Data.Array.Convert.convert t
astSFromR (Ast.AstConstant v) = Ast.AstConstantS $ astSFromR v
astSFromR (Ast.AstLetADShare l v) = Ast.AstLetADShareS l $ astSFromR v
astSFromR (Ast.AstRFromS @sh1 v) =
  case sameShape @sh1 @sh of
    Just Refl -> v
    _ -> error "astSFromR: different ranks in SFromR(RFromS)"
astSFromR v = Ast.AstSFromR v

astPrimalPart :: (GoodScalar r, KnownNat n)
              => AstRanked FullSpan r n -> AstRanked PrimalSpan r n
astPrimalPart t = case t of
  Ast.AstVar{} -> Ast.AstPrimalPart t  -- the only normal form
  Ast.AstLet var u v -> astLet var u (astPrimalPart v)
  AstN1 opCode u -> AstN1 opCode (astPrimalPart u)
  AstN2 opCode u v -> AstN2 opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstR1 opCode u -> Ast.AstR1 opCode (astPrimalPart u)
  Ast.AstR2 opCode u v -> Ast.AstR2 opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2 opCode u v -> Ast.AstI2 opCode (astPrimalPart u) (astPrimalPart v)
  AstSumOfList args -> astSumOfList (map astPrimalPart args)
  Ast.AstIndex v ix -> astIndexR (astPrimalPart v) ix
  Ast.AstSum v -> astSum (astPrimalPart v)
  Ast.AstScatter sh v (var, ix) -> astScatter sh (astPrimalPart v) (var, ix)
  Ast.AstFromList l -> astFromList (map astPrimalPart l)
  Ast.AstFromVector l -> astFromVector (V.map astPrimalPart l)
  Ast.AstReplicate k v -> astReplicate k (astPrimalPart v)
  Ast.AstAppend x y -> astAppend (astPrimalPart x) (astPrimalPart y)
  Ast.AstSlice i k v -> astSlice i k (astPrimalPart v)
  Ast.AstReverse v -> astReverse (astPrimalPart v)
  Ast.AstTranspose perm v -> astTranspose perm (astPrimalPart v)
  Ast.AstReshape sh v -> astReshape sh (astPrimalPart v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, astPrimalPart v)
  Ast.AstGather sh v (vars, ix) -> astGatherR sh (astPrimalPart v) (vars, ix)
  Ast.AstCast v -> astCast $ astPrimalPart v
  Ast.AstLetHVectorIn vars l v -> astLetHVectorIn vars l (astPrimalPart v)
  Ast.AstLetHFunIn var f v -> astLetHFunIn var f (astPrimalPart v)
  Ast.AstRFromS v -> astRFromS $ astPrimalPartS v
  Ast.AstConstant v -> v
  Ast.AstD u _ -> u
  Ast.AstCond b a2 a3 -> astCond b (astPrimalPart a2) (astPrimalPart a3)

astPrimalPartS :: (GoodScalar r, Sh.Shape sh)
               => AstShaped FullSpan r sh -> AstShaped PrimalSpan r sh
astPrimalPartS t = case t of
  Ast.AstVarS{} -> Ast.AstPrimalPartS t  -- the only normal form
  Ast.AstLetS var u v -> astLetS var u (astPrimalPartS v)
  AstN1S opCode u -> AstN1S opCode (astPrimalPartS u)
  AstN2S opCode u v -> AstN2S opCode (astPrimalPartS u) (astPrimalPartS v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astPrimalPartS u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (astPrimalPartS u)
                                             (astPrimalPartS v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (astPrimalPartS u)
                                             (astPrimalPartS v)
  AstSumOfListS args -> astSumOfListS (map astPrimalPartS args)
  Ast.AstIndexS v ix -> Ast.AstIndexS (astPrimalPartS v) ix
  Ast.AstSumS v -> astSumS (astPrimalPartS v)
  Ast.AstScatterS v (var, ix) -> astScatterS (astPrimalPartS v) (var, ix)
  Ast.AstFromListS l -> astFromListS (map astPrimalPartS l)
  Ast.AstFromVectorS l -> astFromVectorS (V.map astPrimalPartS l)
  Ast.AstReplicateS v -> astReplicateS (astPrimalPartS v)
  Ast.AstAppendS x y -> astAppendS (astPrimalPartS x) (astPrimalPartS y)
  Ast.AstSliceS @i v -> astSliceS @i (astPrimalPartS v)
  Ast.AstReverseS v -> astReverseS (astPrimalPartS v)
  Ast.AstTransposeS @perm v -> astTransposeS @perm (astPrimalPartS v)
  Ast.AstReshapeS v -> astReshapeS (astPrimalPartS v)
  Ast.AstBuild1S (var, v) -> Ast.AstBuild1S (var, astPrimalPartS v)
  Ast.AstGatherS v (vars, ix) -> astGatherS (astPrimalPartS v) (vars, ix)
  Ast.AstCastS v -> astCastS $ astPrimalPartS v
  Ast.AstLetHVectorInS vars l v ->
    astLetHVectorInS vars l (astPrimalPartS v)
  Ast.AstLetHFunInS var f v -> astLetHFunInS var f (astPrimalPartS v)
  Ast.AstSFromR v -> astSFromR $ astPrimalPart v
  Ast.AstConstantS v -> v
  Ast.AstDS u _ -> u
  Ast.AstCondS b a2 a3 -> astCondS b (astPrimalPartS a2) (astPrimalPartS a3)

-- Note how this can't be pushed down, say, multiplication, because it
-- multiplies the dual part by the primal part. Addition is fine, though.
astDualPart :: (GoodScalar r, KnownNat n)
            => AstRanked FullSpan r n -> AstRanked DualSpan r n
astDualPart t = case t of
  Ast.AstVar{} -> Ast.AstDualPart t
  Ast.AstLet var u v -> astLet var u (astDualPart v)
  AstN1{} -> Ast.AstDualPart t  -- stuck; the ops are not defined on dual part
  AstN2{} -> Ast.AstDualPart t  -- stuck; the ops are not defined on dual part
  Ast.AstR1{} -> Ast.AstDualPart t
  Ast.AstR2{} -> Ast.AstDualPart t
  Ast.AstI2{} -> Ast.AstDualPart t
  AstSumOfList args -> astSumOfList (map astDualPart args)
  Ast.AstIndex v ix -> astIndexR (astDualPart v) ix
  Ast.AstSum v -> astSum (astDualPart v)
  Ast.AstScatter sh v (var, ix) -> astScatter sh (astDualPart v) (var, ix)
  Ast.AstFromList l -> astFromList (map astDualPart l)
  Ast.AstFromVector l -> astFromVector (V.map astDualPart l)
  Ast.AstReplicate k v -> astReplicate k (astDualPart v)
  Ast.AstAppend x y -> astAppend (astDualPart x) (astDualPart y)
  Ast.AstSlice i k v -> astSlice i k (astDualPart v)
  Ast.AstReverse v -> astReverse (astDualPart v)
  Ast.AstTranspose perm v -> astTranspose perm (astDualPart v)
  Ast.AstReshape sh v -> astReshape sh (astDualPart v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, astDualPart v)
  Ast.AstGather sh v (vars, ix) -> astGatherR sh (astDualPart v) (vars, ix)
  Ast.AstCast v -> astCast $ astDualPart v
  Ast.AstLetHVectorIn vars l v -> astLetHVectorIn vars l (astDualPart v)
  Ast.AstLetHFunIn var f v -> astLetHFunIn var f (astDualPart v)
  Ast.AstRFromS v -> astRFromS $ astDualPartS v
  Ast.AstConstant{}  -> Ast.AstDualPart t  -- this equals nil (not primal 0)
  Ast.AstD _ u' -> u'
  Ast.AstCond b a2 a3 -> astCond b (astDualPart a2) (astDualPart a3)

astDualPartS :: (GoodScalar r, Sh.Shape sh)
             => AstShaped FullSpan r sh -> AstShaped DualSpan r sh
astDualPartS t = case t of
  Ast.AstVarS{} -> Ast.AstDualPartS t
  Ast.AstLetS var u v -> astLetS var u (astDualPartS v)
  AstN1S{} -> Ast.AstDualPartS t
  AstN2S{} -> Ast.AstDualPartS t
  Ast.AstR1S{} -> Ast.AstDualPartS t
  Ast.AstR2S{} -> Ast.AstDualPartS t
  Ast.AstI2S{} -> Ast.AstDualPartS t
  AstSumOfListS args -> astSumOfListS (map astDualPartS args)
  Ast.AstIndexS v ix -> Ast.AstIndexS (astDualPartS v) ix
  Ast.AstSumS v -> astSumS (astDualPartS v)
  Ast.AstScatterS v (var, ix) -> astScatterS (astDualPartS v) (var, ix)
  Ast.AstFromListS l -> astFromListS (map astDualPartS l)
  Ast.AstFromVectorS l -> astFromVectorS (V.map astDualPartS l)
  Ast.AstReplicateS v -> astReplicateS (astDualPartS v)
  Ast.AstAppendS x y -> astAppendS (astDualPartS x) (astDualPartS y)
  Ast.AstSliceS @i v -> astSliceS @i (astDualPartS v)
  Ast.AstReverseS v -> astReverseS (astDualPartS v)
  Ast.AstTransposeS @perm v -> astTransposeS @perm (astDualPartS v)
  Ast.AstReshapeS v -> astReshapeS (astDualPartS v)
  Ast.AstBuild1S (var, v) -> Ast.AstBuild1S (var, astDualPartS v)
  Ast.AstGatherS v (vars, ix) -> astGatherS (astDualPartS v) (vars, ix)
  Ast.AstCastS v -> astCastS $ astDualPartS v
  Ast.AstLetHVectorInS var f v -> astLetHVectorInS var f (astDualPartS v)
  Ast.AstLetHFunInS var f v -> astLetHFunInS var f (astDualPartS v)
  Ast.AstSFromR v -> astSFromR $ astDualPart v
  Ast.AstConstantS{}  -> Ast.AstDualPartS t  -- this equals nil (not primal 0)
  Ast.AstDS _ u' -> u'
  Ast.AstCondS b a2 a3 -> astCondS b (astDualPartS a2) (astDualPartS a3)

astHApply :: forall s. AstSpan s
          => AstHFun -> [HVector (AstRanked s)] -> AstHVector s
astHApply t ll = case t of
  Ast.AstLambda ~(vvars, l) -> case sameAstSpan @s @PrimalSpan of
    Just Refl ->
      foldr (\(vars, l2) -> astLetHVectorInHVector vars (Ast.AstMkHVector l2))
            l (zip vvars ll)
    _ -> Ast.AstHApply t ll
  Ast.AstVarHFun{} -> Ast.AstHApply t ll

-- Inlining doesn't work for this let constructor, because it has many
-- variables, so we try to reduce it to another for which it works.
astLetHVectorInHVector
  :: forall s s2. (AstSpan s, AstSpan s2)
  => [AstDynamicVarName] -> AstHVector s
  -> AstHVector s2
  -> AstHVector s2
astLetHVectorInHVector vars u v =
  case u of
      Ast.AstMkHVector l3 -> assert (length vars == V.length l3) $
        foldr (mapRankedShaped astLetInHVector astLetInHVectorS)
              v (zip vars (V.toList l3))
      Ast.AstLetHVectorInHVector{} -> Ast.AstLetHVectorInHVector vars u v
      Ast.AstLetInHVector var2 u2 d2 ->
        astLetInHVector var2 u2
        $ astLetHVectorInHVector vars d2 v
      Ast.AstLetInHVectorS @sh3 var2 u2 d2 ->
        astLetInHVectorS var2 u2
        $ astLetHVectorInHVector vars d2 v
      _ -> Ast.AstLetHVectorInHVector vars u v

mapRankedShaped
  :: AstSpan s
  => (forall n r. (KnownNat n, GoodScalar r)
      => AstVarName (AstRanked s) r n -> AstRanked s r n -> acc
      -> acc)
  -> (forall sh r. (Sh.Shape sh, GoodScalar r)
      => AstVarName (AstShaped s) r sh -> AstShaped s r sh -> acc
      -> acc)
  -> (AstDynamicVarName, AstDynamic s)
  -> acc
  -> acc
{-# INLINE mapRankedShaped #-}
mapRankedShaped fRanked fShaped
                vd@(AstDynamicVarName @ty @r3 @sh3 varId, d) acc = case d of
  DynamicRanked @r4 @n4 v3
    | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
    , Just Refl <- matchingRank @sh3 @n4
    , Just Refl <- testEquality (typeRep @r3) (typeRep @r4) ->
        fRanked (AstVarName varId) v3 acc
  DynamicShaped @r4 @sh4 v3
    | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
    , Just Refl <- sameShape @sh3 @sh4
    , Just Refl <- testEquality (typeRep @r3) (typeRep @r4) ->
        fShaped (AstVarName varId) v3 acc
  DynamicRankedDummy @r4 @sh4 _ _
    | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
    , Just Refl <- sameShape @sh3 @sh4
    , Just Refl <- testEquality (typeRep @r3) (typeRep @r4) ->
        withListSh (Proxy @sh3) $ \_ ->
          fRanked (AstVarName varId) (astRFromS @sh3 @_ @r3 0) acc
  DynamicShapedDummy @r4 @sh4 _ _
    | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
    , Just Refl <- sameShape @sh3 @sh4
    , Just Refl <- testEquality (typeRep @r3) (typeRep @r4) ->
        fShaped @sh4 @r4 (AstVarName varId) 0 acc
  _ -> error $ "mapRankedShaped: corrupted arguments"
               `showFailure`
               ( vd, typeRep @ty, typeRep @r3, Sh.shapeT @sh3
               , scalarDynamic d, rankDynamic d )

-- Inlining works for this let constructor, because it has just one variable,
-- unlike astLetHVectorIn, etc., so we don't try to eliminate it.
astLetInHVector :: forall n r s s2.
                   (KnownNat n, GoodScalar r, AstSpan s, AstSpan s2)
                => AstVarName (AstRanked s) r n -> AstRanked s r n
                -> AstHVector s2
                -> AstHVector s2
astLetInHVector var u v | astIsSmall True u =
  substituteAstHVector (SubstitutionPayloadRanked u) var v
astLetInHVector var u v = Ast.AstLetInHVector var u v

-- Inlining works for this let constructor, because it has just one variable,
-- unlike astLetHVectorIn, etc., so we don't try to eliminate it.
astLetInHVectorS :: forall sh r s s2.
                    (GoodScalar r, Sh.Shape sh, AstSpan s, AstSpan s2)
                 => AstVarName (AstShaped s) r sh -> AstShaped s r sh
                 -> AstHVector s2
                 -> AstHVector s2
astLetInHVectorS var u v | astIsSmallS True u =
  substituteAstHVector (SubstitutionPayloadShaped u) var v
astLetInHVectorS var u v = Ast.AstLetInHVectorS var u v

-- Inlining doesn't work for this let constructor, because it has many
-- variables, so we try to reduce it to another for which it works.
astLetHVectorIn
  :: forall n r s s2. (KnownNat n, GoodScalar r, AstSpan s, AstSpan s2)
  => [AstDynamicVarName] -> AstHVector s
  -> AstRanked s2 r n
  -> AstRanked s2 r n
astLetHVectorIn vars l v =
  let sh = shapeAst v
  in Sh.withShapeP (shapeToList sh) $ \proxy -> case proxy of
    Proxy @sh | Just Refl <- matchingRank @sh @n -> case l of
      Ast.AstMkHVector l3 ->
        let f :: forall sh1 r1. (Sh.Shape sh1, GoodScalar r1)
              => AstVarName (AstShaped s) r1 sh1 -> AstShaped s r1 sh1
              -> AstRanked s2 r n
              -> AstRanked s2 r n
            f var t acc = astRFromS @sh $ astLetS var t $ astSFromR acc
        in foldr (mapRankedShaped astLet f) v (zip vars (V.toList l3))
      Ast.AstLetHVectorInHVector vars2 d1 d2 ->
        astLetHVectorIn vars2 d1
        $ astLetHVectorIn vars d2 v
      Ast.AstLetInHVector var2 u2 d2 ->
        astLet var2 u2
        $ astLetHVectorIn vars d2 v
      Ast.AstLetInHVectorS @sh3 var2 u2 d2 ->
        astRFromS $ astLetS var2 u2 $ astSFromR @sh
        $ astLetHVectorIn vars d2 v
      _ -> Ast.AstLetHVectorIn vars l v
    _ -> error "astLetHVectorIn: wrong rank of the argument"

-- Inlining doesn't work for this let constructor, because it has many
-- variables, so we try to reduce it to another for which it works.
astLetHVectorInS
  :: forall sh r s s2. (Sh.Shape sh, GoodScalar r, AstSpan s, AstSpan s2)
  => [AstDynamicVarName] -> AstHVector s
  -> AstShaped s2 r sh
  -> AstShaped s2 r sh
astLetHVectorInS vars l v =
  withListSh (Proxy @sh) $ \(_ :: ShapeInt n) -> case l of
    Ast.AstMkHVector l3 ->
      let f :: forall n1 r1. (KnownNat n1, GoodScalar r1)
            => AstVarName (AstRanked s) r1 n1 -> AstRanked s r1 n1
            -> AstShaped s2 r sh
            -> AstShaped s2 r sh
          f var t acc = astSFromR $ astLet var t $ astRFromS acc
      in foldr (mapRankedShaped f astLetS) v (zip vars (V.toList l3))
    Ast.AstLetHVectorInHVector vars2 d1 d2 ->
      astLetHVectorInS vars2 d1
      $ astLetHVectorInS vars d2 v
    Ast.AstLetInHVector var2 u2 d2 ->
      astSFromR $ astLet var2 u2 $ astRFromS
      $ astLetHVectorInS vars d2 v
    Ast.AstLetInHVectorS @sh3 var2 u2 d2 ->
      astLetS var2 u2
      $ astLetHVectorInS vars d2 v
    _ -> Ast.AstLetHVectorInS vars l v

-- Inlining works for this let constructor, because it has just one variable,
-- unlike astLetHVectorIn, etc., so we don't try to eliminate it.
-- We assume functions are never small enough to justify inlining on the spot.
astLetHFunIn
  :: forall n r s.
     AstVarId -> AstHFun -> AstRanked s r n -> AstRanked s r n
astLetHFunIn = Ast.AstLetHFunIn

astLetHFunInS
  :: forall sh r s.
     AstVarId -> AstHFun -> AstShaped s r sh -> AstShaped s r sh
astLetHFunInS = Ast.AstLetHFunInS

astLetHFunInHVector
  :: AstVarId -> AstHFun -> AstHVector s -> AstHVector s
astLetHFunInHVector = Ast.AstLetHFunInHVector


-- * The simplifying bottom-up pass

-- | This function guarantees full simplification: every redex
-- is visited and each combinator applied. The most exhaustive and costly
-- variants of each combinator are used, e.g., astIndexR.
simplifyAst
  :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
  => AstRanked s r n -> AstRanked s r n
simplifyAst t = case t of
  Ast.AstVar{} -> t
  Ast.AstLet var u v -> astLet var (simplifyAst u) (simplifyAst v)
  Ast.AstLetADShare{} -> error "simplifyAst: AstLetADShare"
  Ast.AstCond b a2 a3 ->
    astCond (simplifyAstBool b) (simplifyAst a2) (simplifyAst a3)
  Ast.AstMinIndex a -> Ast.AstMinIndex (simplifyAst a)
  Ast.AstMaxIndex a -> Ast.AstMaxIndex (simplifyAst a)
  Ast.AstFloor a -> Ast.AstFloor (simplifyAst a)
  Ast.AstIota -> t
  AstN1 opCode u ->
    case isRankedInt u of
      Just Refl -> simplifyAstNumOp1 opCode (simplifyAst u)
      _ -> AstN1 opCode (simplifyAst u)
  AstN2 opCode u v ->
    case isRankedInt u of
      Just Refl -> simplifyAstNumOp2 opCode (simplifyAst u) (simplifyAst v)
      _ -> AstN2 opCode (simplifyAst u) (simplifyAst v)
  Ast.AstR1 opCode u -> Ast.AstR1 opCode (simplifyAst u)
  Ast.AstR2 opCode u v -> Ast.AstR2 opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2 opCode u v ->
    case isRankedInt u of
      Just Refl -> simplifyAstIntegralOp2 opCode (simplifyAst u) (simplifyAst v)
      _ -> Ast.AstI2 opCode (simplifyAst u) (simplifyAst v)
  AstSumOfList args ->
    case isRankedInt t of
      Just Refl -> foldr1 simplifyAstPlusOp (map simplifyAst args)
      _ -> astSumOfList (map simplifyAst args)
  Ast.AstIndex v ix -> astIndexR (simplifyAst v) (fmap simplifyAst ix)
  Ast.AstSum v -> astSum (simplifyAst v)
  Ast.AstScatter sh v (var, ix) ->
    astScatter sh (simplifyAst v) (var, fmap simplifyAst ix)
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
          u@(Ast.AstTranspose _ (AstN1 _ w)) | isVar w -> u  -- normal form
          u@(Ast.AstTranspose _ AstN2{}) -> u  -- normal form
          u@(Ast.AstTranspose _ (Ast.AstR1 _ w)) | isVar w -> u
          u@(Ast.AstTranspose _ Ast.AstR2{}) -> u
          u@(Ast.AstTranspose _ AstSumOfList{}) -> u  -- normal form
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
          u@(Ast.AstReshape _ (AstN1 _ w)) | isVar w -> u
          u@(Ast.AstReshape _ AstN2{}) -> u
              -- normal form, because gather doesn't go inside AstN2 either
          u@(Ast.AstReshape _ (Ast.AstR1 _ w)) | isVar w -> u
          u@(Ast.AstReshape _ Ast.AstR2{}) -> u
          u@(Ast.AstReshape _ AstSumOfList{}) -> u  -- normal form
          u@(Ast.AstReshape _ Ast.AstScatter{}) -> u  -- normal form
          -- Not a normal form, because often AstReshape scan be eliminated:
          -- u@(Ast.AstReshape _ Ast.AstReplicate{}) -> u  -- normal form
          Ast.AstReshape sh3 v3 -> astReshapeAsGather sh3 v3
            -- this is terribly expensive, but the only way to fully simplify
          u -> simplifyAst u
      u -> simplifyAst u
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, simplifyAst v)
  Ast.AstGather sh v (vars, ix) ->
    astGatherR sh (simplifyAst v) (vars, fmap simplifyAst ix)
  Ast.AstCast v -> astCast $ simplifyAst v
  Ast.AstFromIntegral v -> astFromIntegral $ simplifyAst v
  AstConst{} -> t
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars (simplifyAstHVector l) (simplifyAst v)
  Ast.AstLetHFunIn var f v ->
    astLetHFunIn var (simplifyAstHFun f) (simplifyAst v)
  Ast.AstRFromS v -> astRFromS $ simplifyAstS v
  Ast.AstConstant v -> Ast.AstConstant (simplifyAst v)
  Ast.AstPrimalPart v -> astPrimalPart (simplifyAst v)
  Ast.AstDualPart v -> astDualPart (simplifyAst v)
  Ast.AstD u u' -> Ast.AstD (simplifyAst u) (simplifyAst u')

simplifyAstS
  :: (Sh.Shape sh, GoodScalar r, AstSpan s)
  => AstShaped s r sh -> AstShaped s r sh
simplifyAstS t = case t of
  Ast.AstVarS{} -> t
  Ast.AstLetS var u v -> astLetS var (simplifyAstS u) (simplifyAstS v)
  Ast.AstLetADShareS{} -> error "simplifyAstS: AstLetADShareS"
  Ast.AstCondS b a2 a3 ->
    astCondS (simplifyAstBool b) (simplifyAstS a2) (simplifyAstS a3)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (simplifyAstS a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (simplifyAstS a)
  Ast.AstFloorS a -> Ast.AstFloorS (simplifyAstS a)
  Ast.AstIotaS -> t
  AstN1S opCode u -> AstN1S opCode (simplifyAstS u)
  AstN2S opCode u v -> AstN2S opCode (simplifyAstS u) (simplifyAstS v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (simplifyAstS u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (simplifyAstS u) (simplifyAstS v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (simplifyAstS u) (simplifyAstS v)
  AstSumOfListS args -> astSumOfListS (map simplifyAstS args)
  Ast.AstIndexS v ix ->
    Ast.AstIndexS (simplifyAstS v) (fmap simplifyAst ix)  -- TODO
  Ast.AstSumS v -> astSumS (simplifyAstS v)
  Ast.AstScatterS v (var, ix) ->
    astScatterS (simplifyAstS v) (var, fmap simplifyAst ix)
  Ast.AstFromListS l -> astFromListS (map simplifyAstS l)
  Ast.AstFromVectorS l -> astFromVectorS (V.map simplifyAstS l)
  Ast.AstReplicateS v -> astReplicateS (simplifyAstS v)
  Ast.AstAppendS x y -> astAppendS (simplifyAstS x) (simplifyAstS y)
  Ast.AstSliceS @i v -> astSliceS @i (simplifyAstS v)
  Ast.AstReverseS v -> astReverseS (simplifyAstS v)
  Ast.AstTransposeS @perm v -> astTransposeS @perm $ simplifyAstS v
  Ast.AstReshapeS v -> astReshapeS $ simplifyAstS v
  Ast.AstBuild1S (var, v) -> Ast.AstBuild1S (var, simplifyAstS v)
  Ast.AstGatherS v (vars, ix) ->
    astGatherS (simplifyAstS v) (vars, fmap simplifyAst ix)
  Ast.AstCastS v -> astCastS $ simplifyAstS v
  Ast.AstFromIntegralS v -> astFromIntegralS $ simplifyAstS v
  AstConstS{} -> t
  Ast.AstLetHVectorInS vars l v ->
    astLetHVectorInS vars (simplifyAstHVector l) (simplifyAstS v)
  Ast.AstLetHFunInS var f v ->
    astLetHFunInS var (simplifyAstHFun f) (simplifyAstS v)
  Ast.AstSFromR v -> astSFromR $ simplifyAst v
  Ast.AstConstantS v -> Ast.AstConstantS (simplifyAstS v)
  Ast.AstPrimalPartS v -> astPrimalPartS (simplifyAstS v)
  Ast.AstDualPartS v -> astDualPartS (simplifyAstS v)
  Ast.AstDS u u' -> Ast.AstDS (simplifyAstS u) (simplifyAstS u')

simplifyAstDynamic
  :: AstSpan s
  => AstDynamic s -> AstDynamic s
simplifyAstDynamic (DynamicRanked u) =
  DynamicRanked $ simplifyAst u
simplifyAstDynamic (DynamicShaped u) =
  DynamicShaped $ simplifyAstS u
simplifyAstDynamic u@DynamicRankedDummy{} = u
simplifyAstDynamic u@DynamicShapedDummy{} = u

simplifyAstHVector
  :: AstSpan s => AstHVector s -> AstHVector s
simplifyAstHVector = \case
  Ast.AstMkHVector l -> Ast.AstMkHVector $ V.map simplifyAstDynamic l
  Ast.AstHApply t ll -> astHApply (simplifyAstHFun t)
                                  (map (V.map simplifyAstDynamic) ll)
  Ast.AstLetHVectorInHVector vars u v ->
    astLetHVectorInHVector vars (simplifyAstHVector u) (simplifyAstHVector v)
  Ast.AstLetHFunInHVector var f v ->
    astLetHFunInHVector var (simplifyAstHFun f) (simplifyAstHVector v)
  Ast.AstLetInHVector var u v ->
    astLetInHVector var (simplifyAst u) (simplifyAstHVector v)
  Ast.AstLetInHVectorS var u v ->
    astLetInHVectorS var (simplifyAstS u) (simplifyAstHVector v)
  Ast.AstBuildHVector1 k (var, v) ->
    Ast.AstBuildHVector1 k (var, simplifyAstHVector v)
  Ast.AstMapAccumRDer k accShs bShs eShs f df rf acc0 es ->
    Ast.AstMapAccumRDer k accShs bShs eShs
                        (simplifyAstHFun f)
                        (simplifyAstHFun df)
                        (simplifyAstHFun rf)
                        (simplifyAstHVector acc0)
                        (simplifyAstHVector es)
  Ast.AstMapAccumLDer k accShs bShs eShs f df rf acc0 es ->
    Ast.AstMapAccumLDer k accShs bShs eShs
                        (simplifyAstHFun f)
                        (simplifyAstHFun df)
                        (simplifyAstHFun rf)
                        (simplifyAstHVector acc0)
                        (simplifyAstHVector es)

simplifyAstHFun :: AstHFun -> AstHFun
simplifyAstHFun = \case
  Ast.AstLambda ~(vvars, l) -> Ast.AstLambda (vvars, simplifyAstHVector l)
  t@(Ast.AstVarHFun{}) -> t

simplifyAstBool :: AstBool -> AstBool
simplifyAstBool t = case t of
  Ast.AstBoolNot (AstBoolConst b) -> AstBoolConst $ not b
  Ast.AstBoolNot arg -> Ast.AstBoolNot $ simplifyAstBool arg
  Ast.AstB2 opCodeBool arg1 arg2 ->
    simplifyAstB2 opCodeBool (simplifyAstBool arg1) (simplifyAstBool arg2)
  AstBoolConst{} -> t
  Ast.AstRel opCodeRel arg1 arg2 ->
    simplifyRelOp opCodeRel (simplifyAst arg1) (simplifyAst arg2)
      -- These expressions potentially represent large tensors that are
      -- expensive to compute even when constant so we simplify and ignore them,
      -- because computation should be done on GPU, not on CPU when simplifying;
      -- we'd need a flag to control how much we pre-compute.
      -- Anyway, because these tensors sometimes represent indexes,
      -- we simplify them a bit more than the shaped ones.
  Ast.AstRelS opCodeRel arg1 arg2 ->
    Ast.AstRelS opCodeRel (simplifyAstS arg1) (simplifyAstS arg2)

-- TODO: when we have more tests, try to limit this rewrite
-- (or only the first half) to Int64 at rank 0 and see if performance improves
-- even more.
simplifyRelOp :: (KnownNat n, GoodScalar r)
              => OpCodeRel
              -> AstRanked PrimalSpan r n -> AstRanked PrimalSpan r n
              -> AstBool
simplifyRelOp EqOp (AstConst u) (AstConst v) = AstBoolConst $ u == v
simplifyRelOp NeqOp (AstConst u) (AstConst v) = AstBoolConst $ u /= v
simplifyRelOp LeqOp (AstConst u) (AstConst v) = AstBoolConst $ u <= v
simplifyRelOp GeqOp (AstConst u) (AstConst v) = AstBoolConst $ u >= v
simplifyRelOp LsOp (AstConst u) (AstConst v) = AstBoolConst $ u < v
simplifyRelOp GtOp (AstConst u) (AstConst v) = AstBoolConst $ u > v
simplifyRelOp EqOp (Ast.AstVar _ u) (Ast.AstVar _ v) | u == v =
  AstBoolConst True
simplifyRelOp LeqOp (Ast.AstVar _ u) (Ast.AstVar _ v) | u == v =
  AstBoolConst True
simplifyRelOp GeqOp (Ast.AstVar _ u) (Ast.AstVar _ v) | u == v =
  AstBoolConst True
simplifyRelOp NeqOp (Ast.AstVar _ u) (Ast.AstVar _ v) | u == v =
  AstBoolConst False
simplifyRelOp LsOp (Ast.AstVar _ u) (Ast.AstVar _ v) | u == v =
  AstBoolConst False
simplifyRelOp GtOp (Ast.AstVar _ u) (Ast.AstVar _ v) | u == v =
  AstBoolConst False
simplifyRelOp opCodeRel arg1 arg2 = Ast.AstRel opCodeRel arg1 arg2

-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right
-- and let's push negation down.
--
-- | Normally, we wouldn't simplify tensor arithmetic so much, but some
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
-- Rank has to be 0 so that the value expressions @0@ below don't crash.
--
-- Several first paragraphs are modelled on @Num@ instance for @AstRanked@
-- and depend on the normal form where @AstConst@, if any, is the first element
-- and the list if fully flattened and of length >= 2.
-- Additionally we here ensure the @AstConst@ is never zero.
--
-- Not considered are rules that would require comparing non-constant terms
-- or that would duplicate a non-constant term, as well as most rules
-- informed by inequalities, expressed via max or min, such as
-- max n (signum (abs x)) | n <= 0 --> signum (abs x).
-- We could use sharing via @rlet@ when terms are duplicated, but it's
-- unclear if the term bloat is worth it.
simplifyAstPlusOp :: AstRanked PrimalSpan Int64 0
                  -> AstRanked PrimalSpan Int64 0
                  -> AstRanked PrimalSpan Int64 0
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
simplifyAstPlusOp (AstN1 NegateOp (Ast.AstVar _ var))
                  (Ast.AstVar _ var')
  | var == var' = 0
simplifyAstPlusOp (Ast.AstVar _ var')
                  (AstN1 NegateOp (Ast.AstVar _ var))
  | var == var' = 0
simplifyAstPlusOp
  (Ast.AstI2 RemOp (AstN1 NegateOp (Ast.AstVar _ var)) (AstConst v))
  (Ast.AstI2 RemOp (Ast.AstVar _ var') (AstConst v'))
  | var == var' && v == v' = 0
simplifyAstPlusOp
  (Ast.AstI2 RemOp (Ast.AstVar _ var') (AstConst v'))
  (Ast.AstI2 RemOp (AstN1 NegateOp (Ast.AstVar _ var)) (AstConst v))
  | var == var' && v == v' = 0

simplifyAstPlusOp u v = AstSumOfList [u, v]

addConstToList :: OR.Array 0 Int64 -> [AstRanked PrimalSpan Int64 0]
               -> AstRanked PrimalSpan Int64 0
addConstToList _ [] = error "addConstToList: AstSumOfList list too short"
addConstToList arr [i] =
  if OR.allA (== 0) arr then i else AstSumOfList [AstConst arr, i]
addConstToList arr l =
  if OR.allA (== 0) arr then AstSumOfList l else AstSumOfList (AstConst arr : l)

simplifyAstNumOp1 :: OpCodeNum1
                  -> AstRanked PrimalSpan Int64 0
                  -> AstRanked PrimalSpan Int64 0
simplifyAstNumOp1 NegateOp (AstConst u) = AstConst $ negate u
simplifyAstNumOp1 NegateOp (AstSumOfList l) =
  foldr1 simplifyAstPlusOp (map (simplifyAstNumOp1 NegateOp) l)
simplifyAstNumOp1 NegateOp (AstN2 TimesOp (AstConst u) v) =
  simplifyAstNumOp2 TimesOp (AstConst $ negate u) v
    -- given a choice, prefer to negate a constant
simplifyAstNumOp1 NegateOp (AstN2 TimesOp u v) =
  simplifyAstNumOp2 TimesOp u (simplifyAstNumOp1 NegateOp v)
simplifyAstNumOp1 NegateOp (AstN1 NegateOp u) = u
simplifyAstNumOp1 NegateOp (AstN1 SignumOp u) =
  simplifyAstNumOp1 SignumOp (simplifyAstNumOp1 NegateOp u)
simplifyAstNumOp1 NegateOp (Ast.AstI2 QuotOp u v) =
  simplifyAstIntegralOp2 QuotOp (simplifyAstNumOp1 NegateOp u) v
    -- v is likely positive and let's keep it so
simplifyAstNumOp1 NegateOp (Ast.AstI2 RemOp u v) =
  simplifyAstIntegralOp2 RemOp (simplifyAstNumOp1 NegateOp u) v
    -- v is likely positive and let's keep it so

simplifyAstNumOp1 AbsOp (AstConst u) = AstConst $ abs u
simplifyAstNumOp1 AbsOp (AstN1 AbsOp u) = AstN1 AbsOp u
simplifyAstNumOp1 AbsOp (AstN1 NegateOp u) = simplifyAstNumOp1 AbsOp u
simplifyAstNumOp1 SignumOp (AstConst u) = AstConst $ signum u
simplifyAstNumOp1 SignumOp (AstN1 SignumOp u) = AstN1 SignumOp u
simplifyAstNumOp1 SignumOp (AstN1 AbsOp u) =
  simplifyAstNumOp1 AbsOp (AstN1 SignumOp u)

simplifyAstNumOp1 opCode u = AstN1 opCode u

simplifyAstNumOp2 :: OpCodeNum2
                  -> AstRanked PrimalSpan Int64 0
                  -> AstRanked PrimalSpan Int64 0
                  -> AstRanked PrimalSpan Int64 0
simplifyAstNumOp2 MinusOp u v =
  simplifyAstPlusOp u (simplifyAstNumOp1 NegateOp v)
simplifyAstNumOp2 TimesOp (AstConst u) (AstConst v) = AstConst $ u * v
simplifyAstNumOp2 TimesOp (AstConst 0) _v = AstConst 0
simplifyAstNumOp2 TimesOp _u (AstConst 0) = AstConst 0
simplifyAstNumOp2 TimesOp (AstConst 1) v = v
simplifyAstNumOp2 TimesOp u (AstConst 1) = u
{- TODO: is it worth adding AstLet with a fresh variables
   to share w and so make these rules safe? Perhaps after we decide
   a normal form (e.g., a polynomial)?
simplifyAstNumOp TimesOp (AstN2 PlusOp (u, v), w) =
  simplifyAstPlusOp ( simplifyAstNumOp TimesOp (u, w)
                    , simplifyAstNumOp TimesOp (v, w) )
simplifyAstNumOp TimesOp (u, AstN2 PlusOp (v, w)) =
  simplifyAstPlusOp ( simplifyAstNumOp TimesOp (u, v)
                    , simplifyAstNumOp TimesOp (u, w) )
-}
simplifyAstNumOp2 TimesOp (AstSumOfList l) w@AstConst{} =
  foldr1 simplifyAstPlusOp (map (\u -> simplifyAstNumOp2 TimesOp u w) l)
simplifyAstNumOp2 TimesOp u@AstConst{} (AstSumOfList l) =
  foldr1 simplifyAstPlusOp (map (simplifyAstNumOp2 TimesOp u) l)
-- TODO: perhaps aim for a polynomial normal form? but that requires global
-- inspection of the whole expression
simplifyAstNumOp2 TimesOp (AstConst u) (AstN2 TimesOp (AstConst v) w) =
  simplifyAstNumOp2 TimesOp (AstConst $ u * v) w
simplifyAstNumOp2 TimesOp u (AstConst n) =
  simplifyAstNumOp2 TimesOp (AstConst n) u
simplifyAstNumOp2 TimesOp (AstN2 TimesOp u v) w =
  simplifyAstNumOp2 TimesOp u (simplifyAstNumOp2 TimesOp v w)

-- With static shapes, the second argument to QuotOp and RemOp
-- is often a constant, which makes such rules worth including,
-- since they are likely to fire. To help them fire, we avoid changing
-- that constant, if possible, e.g., in rules for NegateOp.
simplifyAstNumOp2
  TimesOp (AstConst v)
          (Ast.AstI2 QuotOp (Ast.AstVar sh var) (AstConst v')) | v == v' =
    simplifyAstNumOp2 MinusOp
                      (Ast.AstVar sh var)
                      (Ast.AstI2 RemOp (Ast.AstVar sh var) (AstConst v))
simplifyAstNumOp2 opCode u v = AstN2 opCode u v

simplifyAstIntegralOp2 :: OpCodeIntegral2
                       -> AstRanked PrimalSpan Int64 0
                       -> AstRanked PrimalSpan Int64 0
                       -> AstRanked PrimalSpan Int64 0
simplifyAstIntegralOp2 QuotOp (AstConst u) (AstConst v) = AstConst $ quot u v
simplifyAstIntegralOp2 QuotOp (AstConst 0) _v = AstConst 0
simplifyAstIntegralOp2 QuotOp u (AstConst 1) = u
simplifyAstIntegralOp2 QuotOp (Ast.AstI2 RemOp _u (AstConst v)) (AstConst v')
  | v' >= v && v >= 0 = 0
simplifyAstIntegralOp2 QuotOp (Ast.AstI2 QuotOp u v) w =
  simplifyAstIntegralOp2 QuotOp u (simplifyAstNumOp2 TimesOp v w)
simplifyAstIntegralOp2 QuotOp (Ast.AstN2 TimesOp (AstConst u) v) (AstConst u')
  | u == u' = v

simplifyAstIntegralOp2 RemOp (AstConst u) (AstConst v) = AstConst $ rem u v
simplifyAstIntegralOp2 RemOp (AstConst 0) _v = 0
simplifyAstIntegralOp2 RemOp _u (AstConst 1) = 0
simplifyAstIntegralOp2 RemOp (Ast.AstI2 RemOp u (AstConst v)) (AstConst v')
  | v' >= v && v >= 0 = Ast.AstI2 RemOp u (AstConst v)
simplifyAstIntegralOp2 RemOp (Ast.AstI2 RemOp u (AstConst v)) (AstConst v')
  | rem v v' == 0 && v > 0 = simplifyAstIntegralOp2 RemOp u (AstConst v')
simplifyAstIntegralOp2 RemOp (AstN2 TimesOp (AstConst u) _v) (AstConst u')
  | rem u u' == 0 = 0

simplifyAstIntegralOp2 opCode u v = Ast.AstI2 opCode u v

-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right.
simplifyAstB2 :: OpCodeBool -> AstBool -> AstBool -> AstBool
simplifyAstB2 AndOp (AstBoolConst True) b = b
simplifyAstB2 AndOp (AstBoolConst False) _b = AstBoolConst False
simplifyAstB2 AndOp b (AstBoolConst True) = b
simplifyAstB2 AndOp _b (AstBoolConst False) = AstBoolConst False
simplifyAstB2 OrOp (AstBoolConst True) _b = AstBoolConst True
simplifyAstB2 OrOp (AstBoolConst False) b = b
simplifyAstB2 OrOp _b (AstBoolConst True) = AstBoolConst True
simplifyAstB2 OrOp b (AstBoolConst False) = b
simplifyAstB2 opCodeBool arg1 arg2 = Ast.AstB2 opCodeBool arg1 arg2


-- * Substitution payload and adaptors for AstVarName

-- | The term to substitute for a variable. Without this variant type,
-- we'd need to duplicate the whole sibstitution code, one copy
-- for each of the cases.
type role SubstitutionPayload nominal nominal
  -- r can't be representational due to AstRanked having it as nominal
data SubstitutionPayload :: AstSpanType -> Type -> Type where
  SubstitutionPayloadRanked :: forall s r n. KnownNat n
                            => AstRanked s r n -> SubstitutionPayload s r
  SubstitutionPayloadShaped :: forall s r sh. Sh.Shape sh
                            => AstShaped s r sh -> SubstitutionPayload s r
  SubstitutionPayloadHFun :: AstHFun -> SubstitutionPayload PrimalSpan Float

-- | We assume no variable is shared between a binding and its nested binding
-- and nobody substitutes into variables that are bound.
-- This keeps the substitution code simple, because we never need to compare
-- variables to any variable in the bindings.
substituteAst :: forall n n2 s s2 r r2 f.
                 ( GoodScalar r, GoodScalar r2, KnownNat n
                 , AstSpan s, AstSpan s2 )
              => SubstitutionPayload s2 r2 -> AstVarName (f s2) r2 n2
              -> AstRanked s r n
              -> AstRanked s r n
substituteAst i (AstVarName varId) v1 = fromMaybe v1 $ substitute1Ast i varId v1

substituteAstIndex
  :: (GoodScalar r2, AstSpan s2)
  => SubstitutionPayload s2 r2 -> AstVarName (AstRanked s2) r2 n2
  -> AstIndex n
  -> AstIndex n
substituteAstIndex i (AstVarName varId) ix =
  fromMaybe ix $ substitute1AstIndex i varId ix

substituteAstS :: forall sh sh2 s2 s r r2 f.
                  ( GoodScalar r, GoodScalar r2, Sh.Shape sh
                  , AstSpan s, AstSpan s2 )
               => SubstitutionPayload s2 r2 -> AstVarName (f s2) r2 sh2
               -> AstShaped s r sh
               -> AstShaped s r sh
substituteAstS i (AstVarName varId) v1 =
  fromMaybe v1 $ substitute1AstS i varId v1

substituteAstIndexS
  :: (GoodScalar r2, AstSpan s2)
  => SubstitutionPayload s2 r2 -> AstVarName (AstRanked s2) r2 n2
  -> AstIndexS sh
  -> AstIndexS sh
substituteAstIndexS i (AstVarName varId) ix =
  fromMaybe ix $ substitute1AstIndexS i varId ix

substituteAstHVector
  :: (GoodScalar r2, AstSpan s, AstSpan s2)
  => SubstitutionPayload s2 r2 -> AstVarName (f s2) r2 y -> AstHVector s
  -> AstHVector s
substituteAstHVector i (AstVarName varId) v1 =
  fromMaybe v1 $ substitute1AstHVector i varId v1


-- * Substitution workers

-- We can't use AstVarName in place of AstVarId, because of the recursive calls,
-- e.g. AstRFromS and AstCast, due to which, the extra type parameters would
-- need to be kept unrelated to anything else (except the existentially bound
-- parameters in SubstitutionPayload, which would need to be checked
-- at runtime).
substitute1Ast :: forall n s s2 r r2.
                  ( GoodScalar r, GoodScalar r2, KnownNat n
                  , AstSpan s, AstSpan s2 )
               => SubstitutionPayload s2 r2 -> AstVarId -> AstRanked s r n
               -> Maybe (AstRanked s r n)
substitute1Ast i var v1 = case v1 of
  Ast.AstVar sh var2 ->
    if fromEnum var == fromEnum var2
    then case i of
      SubstitutionPayloadRanked @_ @_ @m t -> case sameAstSpan @s @s2 of
        Just Refl -> case sameNat (Proxy @m) (Proxy @n) of
          Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
            Just Refl -> assert (shapeAst t == sh `blame` (shapeAst t, sh, t))
                         $ Just t
            _ -> error "substitute1Ast: scalar"
          _ -> error "substitute1Ast: rank"
        _ -> error "substitute1Ast: span"
      -- To impose such checks, we'd need to switch from OD tensors
      -- to existential OR/OS tensors so that we can inspect
      -- which it is and then seed Delta evaluation maps with that.
      -- _ -> error "substitute1Ast: type"
      SubstitutionPayloadShaped @_ @_ @sh2 t -> case sameAstSpan @s @s2 of
        Just Refl -> case shapeToList sh == Sh.shapeT @sh2 of
          True -> case matchingRank @sh2 @n of
            Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
              Just Refl -> Just $ astRFromS t
              _ -> error "substitute1Ast: scalar"
            _ -> error "substitute1Ast: rank"
          False -> error "substitute1Ast: shape"
        _ -> error "substitute1Ast: span"
      SubstitutionPayloadHFun{} -> error "substitute1Ast: unexpected lambda"
    else Nothing
  Ast.AstLet var2 u v ->
    case (substitute1Ast i var u, substitute1Ast i var v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) -> Just $ astLet var2 (fromMaybe u mu) (fromMaybe v mv)
  Ast.AstLetADShare{} -> error "substitute1Ast: AstLetADShare"
  Ast.AstCond b v w ->
    case ( substitute1AstBool i var b
         , substitute1Ast i var v
         , substitute1Ast i var w ) of
      (Nothing, Nothing, Nothing) -> Nothing
      (mb, mv, mw) ->
        Just $ astCond (fromMaybe b mb) (fromMaybe v mv) (fromMaybe w mw)
  Ast.AstMinIndex a -> Ast.AstMinIndex <$> substitute1Ast i var a
  Ast.AstMaxIndex a -> Ast.AstMaxIndex <$> substitute1Ast i var a
  Ast.AstFloor a -> Ast.AstFloor <$> substitute1Ast i var a
  Ast.AstIota -> Nothing
  Ast.AstN1 opCode u ->
    (\u2 -> case isRankedInt u2 of
       Just Refl -> simplifyAstNumOp1 opCode u2
       _ -> Ast.AstN1 opCode u2)
    <$> substitute1Ast i var u
  Ast.AstN2 opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ case isRankedInt u of
         Just Refl -> simplifyAstNumOp2 opCode (fromMaybe u mu) (fromMaybe v mv)
         _ -> Ast.AstN2 opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstR1 opCode u -> Ast.AstR1 opCode <$> substitute1Ast i var u
  Ast.AstR2 opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstR2 opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstI2 opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ case isRankedInt u of
         Just Refl ->
           simplifyAstIntegralOp2 opCode (fromMaybe u mu) (fromMaybe v mv)
         _ -> Ast.AstI2 opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstSumOfList args ->
    let margs = map (substitute1Ast i var) args
    in if any isJust margs
       then Just $ case isRankedInt v1 of
         Just Refl -> foldr1 simplifyAstPlusOp $ zipWith fromMaybe args margs
         _ -> astSumOfList $ zipWith fromMaybe args margs
       else Nothing
  Ast.AstIndex v ix ->
    case (substitute1Ast i var v, substitute1AstIndex i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astIndexR (fromMaybe v mv) (fromMaybe ix mix)
  Ast.AstSum v -> astSum <$> substitute1Ast i var v
  Ast.AstScatter sh v (vars, ix) ->
    case (substitute1Ast i var v, substitute1AstIndex i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astScatter sh (fromMaybe v mv)
                                        (vars, fromMaybe ix mix)
  Ast.AstFromList args ->
    let margs = map (substitute1Ast i var) args
    in if any isJust margs
       then Just $ astFromList $ zipWith fromMaybe args margs
       else Nothing
  Ast.AstFromVector args ->
    let margs = V.map (substitute1Ast i var) args
    in if V.any isJust margs
       then Just $ astFromVector $ V.zipWith fromMaybe args margs
       else Nothing
  Ast.AstReplicate k v -> astReplicate k <$> substitute1Ast i var v
  Ast.AstAppend x y ->
    case (substitute1Ast i var x, substitute1Ast i var y) of
      (Nothing, Nothing) -> Nothing
      (mx, my) -> Just $ astAppend (fromMaybe x mx) (fromMaybe y my)
  Ast.AstSlice i2 n v -> astSlice i2 n <$> substitute1Ast i var v
  Ast.AstReverse v -> astReverse <$> substitute1Ast i var v
  Ast.AstTranspose perm v -> astTranspose perm <$> substitute1Ast i var v
  Ast.AstReshape sh v -> astReshape sh <$> substitute1Ast i var v
  Ast.AstBuild1 k (var2, v) ->
    Ast.AstBuild1 k . (var2,) <$> substitute1Ast i var v
  Ast.AstGather sh v (vars, ix) ->
    case (substitute1Ast i var v, substitute1AstIndex i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astGatherR sh (fromMaybe v mv)
                                        (vars, fromMaybe ix mix)
  Ast.AstCast v -> astCast <$> substitute1Ast i var v
  Ast.AstFromIntegral v -> astFromIntegral <$> substitute1Ast i var v
  Ast.AstConst{} -> Nothing
  Ast.AstLetHVectorIn vars l v ->
    case (substitute1AstHVector i var l, substitute1Ast i var v) of
      (Nothing, Nothing) -> Nothing
      (ml, mv) ->
        Just $ astLetHVectorIn vars (fromMaybe l ml) (fromMaybe v mv)
  Ast.AstLetHFunIn var2 f v ->
    case (substitute1AstHFun i var f, substitute1Ast i var v) of
      (Nothing, Nothing) -> Nothing
      (mf, mv) ->
        Just $ astLetHFunIn var2 (fromMaybe f mf) (fromMaybe v mv)
  Ast.AstRFromS v -> astRFromS <$> substitute1AstS i var v
  Ast.AstConstant a -> Ast.AstConstant <$> substitute1Ast i var a
  Ast.AstPrimalPart a -> astPrimalPart <$> substitute1Ast i var a
  Ast.AstDualPart a -> astDualPart <$> substitute1Ast i var a
  Ast.AstD x y ->
    case (substitute1Ast i var x, substitute1Ast i var y) of
      (Nothing, Nothing) -> Nothing
      (mx, my) -> Just $ Ast.AstD (fromMaybe x mx) (fromMaybe y my)

substitute1AstIndex
  :: (GoodScalar r2, AstSpan s2)
  => SubstitutionPayload s2 r2 -> AstVarId -> AstIndex n
  -> Maybe (AstIndex n)
substitute1AstIndex i var ix =
  let mix = fmap (substitute1Ast i var) ix
  in if any isJust mix
     then Just $ zipWith_Index fromMaybe ix mix
     else Nothing

substitute1AstS :: forall sh s s2 r r2.
                   ( GoodScalar r, GoodScalar r2, Sh.Shape sh
                   , AstSpan s, AstSpan s2 )
                => SubstitutionPayload s2 r2 -> AstVarId -> AstShaped s r sh
                -> Maybe (AstShaped s r sh)
substitute1AstS i var = \case
  Ast.AstVarS var2 ->
    if fromEnum var == fromEnum var2
    then case i of
      SubstitutionPayloadShaped @_ @_ @sh2 t -> case sameAstSpan @s @s2 of
        Just Refl -> case sameShape @sh2 @sh of
          Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
            Just Refl -> Just t
            _ -> error "substitute1AstS: scalar"
          _ -> error "substitute1AstS: shape"
        _ -> error "substitute1AstS: span"
      -- To impose such checks, we'd need to switch from OD tensors
      -- to existential OR/OS tensors so that we can inspect
      -- which it is and then seed Delta evaluation maps with that.
      -- _ -> error "substitute1AstS: type"
      SubstitutionPayloadRanked @_ @_ @m t -> case sameAstSpan @s @s2 of
        Just Refl -> case matchingRank @sh @m of
          Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
            Just Refl -> assert (Sh.shapeT @sh == shapeToList (shapeAst t))
                         $ Just $ astSFromR t
            _ -> error "substitute1AstS: scalar"
          _ -> error "substitute1AstS: rank"
        _ -> error "substitute1AstS: span"
      SubstitutionPayloadHFun{} -> error "substitute1AstS: unexpected lambda"
    else Nothing
  Ast.AstLetS var2 u v ->
    case (substitute1AstS i var u, substitute1AstS i var v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) -> Just $ astLetS var2 (fromMaybe u mu) (fromMaybe v mv)
  Ast.AstLetADShareS{} -> error "substitute1AstS: AstLetADShareS"
  Ast.AstCondS b v w ->
    case ( substitute1AstBool i var b
         , substitute1AstS i var v
         , substitute1AstS i var w ) of
      (Nothing, Nothing, Nothing) -> Nothing
      (mb, mv, mw) ->
        Just $ astCondS (fromMaybe b mb) (fromMaybe v mv) (fromMaybe w mw)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS <$> substitute1AstS i var a
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS <$> substitute1AstS i var a
  Ast.AstFloorS a -> Ast.AstFloorS <$> substitute1AstS i var a
  Ast.AstIotaS -> Nothing
  Ast.AstN1S opCode u -> Ast.AstN1S opCode  <$> substitute1AstS i var u
  Ast.AstN2S opCode u v ->
    let mu = substitute1AstS i var u
        mv = substitute1AstS i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstN2S opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstR1S opCode u -> Ast.AstR1S opCode <$> substitute1AstS i var u
  Ast.AstR2S opCode u v ->
    let mu = substitute1AstS i var u
        mv = substitute1AstS i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstR2S opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstI2S opCode u v ->
    let mu = substitute1AstS i var u
        mv = substitute1AstS i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstI2S opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstSumOfListS args ->
    let margs = map (substitute1AstS i var) args
    in if any isJust margs
       then Just $ astSumOfListS $ zipWith fromMaybe args margs
       else Nothing
  Ast.AstIndexS v ix ->
    case (substitute1AstS i var v, substitute1AstIndexS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astIndexStepS (fromMaybe v mv) (fromMaybe ix mix)
  Ast.AstSumS v -> astSumS <$> substitute1AstS i var v
  Ast.AstScatterS v (vars, ix) ->
    case (substitute1AstS i var v, substitute1AstIndexS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astScatterS (fromMaybe v mv)
                                      (vars, fromMaybe ix mix)
  Ast.AstFromListS args ->
    let margs = map (substitute1AstS i var) args
    in if any isJust margs
       then Just $ astFromListS $ zipWith fromMaybe args margs
       else Nothing
  Ast.AstFromVectorS args ->
    let margs = V.map (substitute1AstS i var) args
    in if V.any isJust margs
       then Just $ astFromVectorS $ V.zipWith fromMaybe args margs
       else Nothing
  Ast.AstReplicateS v -> astReplicateS <$> substitute1AstS i var v
  Ast.AstAppendS x y ->
    case (substitute1AstS i var x, substitute1AstS i var y) of
      (Nothing, Nothing) -> Nothing
      (mx, my) -> Just $ astAppendS (fromMaybe x mx) (fromMaybe y my)
  Ast.AstSliceS @i v -> astSliceS @i <$> substitute1AstS i var v
  Ast.AstReverseS v -> astReverseS <$> substitute1AstS i var v
  Ast.AstTransposeS @perm v -> astTransposeS @perm <$> substitute1AstS i var v
  Ast.AstReshapeS v -> astReshapeS <$> substitute1AstS i var v
  Ast.AstBuild1S (var2, v) ->
    Ast.AstBuild1S . (var2,) <$> substitute1AstS i var v
  Ast.AstGatherS v (vars, ix) ->
    case (substitute1AstS i var v, substitute1AstIndexS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astGatherS (fromMaybe v mv)
                                     (vars, fromMaybe ix mix)
  Ast.AstCastS v -> astCastS <$> substitute1AstS i var v
  Ast.AstFromIntegralS a -> astFromIntegralS <$> substitute1AstS i var a
  Ast.AstConstS{} -> Nothing
  Ast.AstLetHVectorInS vars l v ->
    case (substitute1AstHVector i var l, substitute1AstS i var v) of
      (Nothing, Nothing) -> Nothing
      (ml, mv) ->
        Just $ astLetHVectorInS vars (fromMaybe l ml) (fromMaybe v mv)
  Ast.AstLetHFunInS var2 f v ->
    case (substitute1AstHFun i var f, substitute1AstS i var v) of
      (Nothing, Nothing) -> Nothing
      (mf, mv) ->
        Just $ astLetHFunInS var2 (fromMaybe f mf) (fromMaybe v mv)
  Ast.AstSFromR v -> astSFromR <$> substitute1Ast i var v
  Ast.AstConstantS a -> Ast.AstConstantS <$> substitute1AstS i var a
  Ast.AstPrimalPartS a -> astPrimalPartS <$> substitute1AstS i var a
  Ast.AstDualPartS a -> astDualPartS <$> substitute1AstS i var a
  Ast.AstDS x y ->
    case (substitute1AstS i var x, substitute1AstS i var y) of
      (Nothing, Nothing) -> Nothing
      (mx, my) -> Just $ Ast.AstDS (fromMaybe x mx) (fromMaybe y my)

substitute1AstIndexS
  :: (GoodScalar r2, AstSpan s2)
  => SubstitutionPayload s2 r2 -> AstVarId -> AstIndexS sh
  -> Maybe (AstIndexS sh)
substitute1AstIndexS i var ix =
  let mix = fmap (substitute1Ast i var) ix
  in if any isJust mix
     then Just $ ShapedList.zipWith_Sized fromMaybe ix mix
     else Nothing

substitute1AstDynamic
  :: (GoodScalar r2, AstSpan s, AstSpan s2)
  => SubstitutionPayload s2 r2 -> AstVarId -> AstDynamic s
  -> Maybe (AstDynamic s)
substitute1AstDynamic i var = \case
  DynamicRanked t -> DynamicRanked <$> substitute1Ast i var t
  DynamicShaped t -> DynamicShaped <$> substitute1AstS i var t
  DynamicRankedDummy{} -> Nothing
  DynamicShapedDummy{} -> Nothing

substitute1AstHVector
  :: (GoodScalar r2, AstSpan s, AstSpan s2)
  => SubstitutionPayload s2 r2 -> AstVarId -> AstHVector s
  -> Maybe (AstHVector s)
substitute1AstHVector i var = \case
  Ast.AstMkHVector args ->
    let margs = V.map (substitute1AstDynamic i var) args
    in if V.any isJust margs
       then Just $ Ast.AstMkHVector $ V.zipWith fromMaybe args margs
       else Nothing
  Ast.AstHApply t ll ->
    case ( substitute1AstHFun i var t
         , map (V.map (substitute1AstDynamic i var)) ll ) of
      (Nothing, mll) | all (V.all isNothing) mll -> Nothing
      (mt, mll) ->
        Just $ astHApply (fromMaybe t mt) (zipWith (V.zipWith fromMaybe) ll mll)
  Ast.AstLetHVectorInHVector vars2 u v ->
    case (substitute1AstHVector i var u, substitute1AstHVector i var v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) ->
        Just $ astLetHVectorInHVector vars2 (fromMaybe u mu) (fromMaybe v mv)
  Ast.AstLetHFunInHVector var2 f v ->
    case (substitute1AstHFun i var f, substitute1AstHVector i var v) of
      (Nothing, Nothing) -> Nothing
      (mf, mv) ->
        Just $ astLetHFunInHVector var2 (fromMaybe f mf) (fromMaybe v mv)
  Ast.AstLetInHVector var2 u v ->
    case (substitute1Ast i var u, substitute1AstHVector i var v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) -> Just $ astLetInHVector var2 (fromMaybe u mu) (fromMaybe v mv)
  Ast.AstLetInHVectorS var2 u v ->
    case (substitute1AstS i var u, substitute1AstHVector i var v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) -> Just $ astLetInHVectorS var2 (fromMaybe u mu) (fromMaybe v mv)
  Ast.AstBuildHVector1 k (var2, v) ->
    Ast.AstBuildHVector1 k . (var2,) <$> substitute1AstHVector i var v
  Ast.AstMapAccumRDer k accShs bShs eShs f df rf acc0 es ->
    case ( substitute1AstHFun i var f, substitute1AstHFun i var df
         , substitute1AstHFun i var rf, substitute1AstHVector i var acc0
         , substitute1AstHVector i var es ) of
      (Nothing, Nothing, Nothing, Nothing, Nothing) -> Nothing
      (mf, mdf, mrf, macc0, mes) ->
        Just $ Ast.AstMapAccumRDer k accShs bShs eShs
                                   (fromMaybe f mf)
                                   (fromMaybe df mdf)
                                   (fromMaybe rf mrf)
                                   (fromMaybe acc0 macc0)
                                   (fromMaybe es mes)
  Ast.AstMapAccumLDer k accShs bShs eShs f df rf acc0 es ->
    case ( substitute1AstHFun i var f, substitute1AstHFun i var df
         , substitute1AstHFun i var rf, substitute1AstHVector i var acc0
         , substitute1AstHVector i var es ) of
      (Nothing, Nothing, Nothing, Nothing, Nothing) -> Nothing
      (mf, mdf, mrf, macc0, mes) ->
        Just $ Ast.AstMapAccumLDer k accShs bShs eShs
                                   (fromMaybe f mf)
                                   (fromMaybe df mdf)
                                   (fromMaybe rf mrf)
                                   (fromMaybe acc0 macc0)
                                   (fromMaybe es mes)

substitute1AstHFun
  :: SubstitutionPayload s2 r2 -> AstVarId -> AstHFun
  -> Maybe AstHFun
substitute1AstHFun i var = \case
  Ast.AstLambda{} -> Nothing  -- no outside free variables
  Ast.AstVarHFun _shss _shs var2 ->
    if fromEnum var == fromEnum var2
    then case i of
      SubstitutionPayloadShaped{} ->
        error "substitute1AstHFun: unexpected tensor"
      SubstitutionPayloadRanked{} ->
        error "substitute1AstHFun: unexpected tensor"
      SubstitutionPayloadHFun h -> Just h
    else Nothing

substitute1AstBool :: (GoodScalar r2, AstSpan s2)
                   => SubstitutionPayload s2 r2 -> AstVarId -> AstBool
                   -> Maybe AstBool
substitute1AstBool i var = \case
  Ast.AstBoolNot arg -> Ast.AstBoolNot <$> substitute1AstBool i var arg
    -- this can't be simplified, because constant boolean can't have variables
  Ast.AstB2 opCodeBool arg1 arg2 ->
    let mb1 = substitute1AstBool i var arg1
        mb2 = substitute1AstBool i var arg2
    in if isJust mb1 || isJust mb2
       then Just $ simplifyAstB2 opCodeBool (fromMaybe arg1 mb1)
                                            (fromMaybe arg2 mb2)
       else Nothing
  Ast.AstBoolConst{} -> Nothing
  Ast.AstRel opCodeRel arg1 arg2 ->
    let mr1 = substitute1Ast i var arg1
        mr2 = substitute1Ast i var arg2
    in if isJust mr1 || isJust mr2
       then Just $ simplifyRelOp opCodeRel (fromMaybe arg1 mr1)
                                           (fromMaybe arg2 mr2)
       else Nothing
  Ast.AstRelS opCodeRel arg1 arg2 ->
    let mr1 = substitute1AstS i var arg1
        mr2 = substitute1AstS i var arg2
    in if isJust mr1 || isJust mr2
       then Just $ Ast.AstRelS opCodeRel (fromMaybe arg1 mr1)
                                         (fromMaybe arg2 mr2)
       else Nothing
