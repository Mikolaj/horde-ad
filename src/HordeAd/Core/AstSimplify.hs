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
    normalizePermutation
    -- * The combinators for indexing and gather
  , astNonIndexStep, astNonIndexStepS, astIndexStep, astIndexStepS
  , astGatherStep, astGatherStepS
    -- * The simplifying combinators, one for most AST constructors
  , astLet, astLetS, astCond, astCondS, astSumOfList, astSumOfListS
  , astSum, astSumS, astScatter, astScatterS, astFromVector, astFromVectorS
  , astReplicate, astReplicateS, astAppend, astAppendS, astSlice, astSliceS
  , astReverse, astReverseS
  , astTranspose, astTransposeS, astReshape, astReshapeS
  , astCast, astCastS, astFromIntegral, astFromIntegralS
  , astProject, astProjectS, astRFromS, astSFromR
  , astPrimalPart, astPrimalPartS, astDualPart, astDualPartS
  , astLetHVectorIn, astLetHVectorInS, astLetHFunIn, astLetHFunInS, astHApply
  , astLetHVectorInHVector, astLetHFunInHVector
  , astLetInHVector, astLetInHVectorS
    -- * The simplifying bottom-up pass
  , simplifyAst, simplifyAstHVector, simplifyAstS
    -- * The expanding (to gather expressions) bottom-up pass
  , expandAst, expandAstHVector, expandAstS
    -- * Substitution payload and adaptors for AstVarName
  , SubstitutionPayload(..)
  , substituteAst, substitute1Ast, substituteAstIndex
  , substituteAstS, substitute1AstS, substituteAstIndexS
  , substituteAstHVector, substitute1AstHVector
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (mapAndUnzipM)
import qualified Data.Array.Convert
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Mixed as X
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Functor.Const
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
import           HordeAd.Core.HVectorOps
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.BackendConcrete
import           HordeAd.Internal.OrthotopeOrphanInstances
  (FlipS (..), MapSucc, trustMeThisIsAPermutation)
import           HordeAd.Util.ShapedList
  (pattern (:.$), pattern (::$), pattern ZIS, pattern ZS)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedList

data SimplifyKnobs = SimplifyKnobs
  { knobStepOnly :: Bool
  , knobExpand   :: Bool
  }

defaultKnobs :: SimplifyKnobs
defaultKnobs = SimplifyKnobs False False


-- * Expressing operations as Gather; introduces new variable names

-- We keep AstTranspose terms for as long as possible, because
-- they are small and fuse nicely in many cases. For some forms of indexing
-- and nesting with reshape and gather they don't fuse, which is when
-- this function is invoked.
astTransposeAsGather
  :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
  => SimplifyKnobs -> Permutation -> AstRanked s r n -> AstRanked s r n
{-# NOINLINE astTransposeAsGather #-}
astTransposeAsGather knobs perm v =
  let pInt = length perm
  in case someNatVal $ toInteger pInt of
    Just (SomeNat @p _) -> do
      funToVarsIx pInt $ \ (!vars, !ix) ->
        let asts :: AstIndex p
            asts = permutePrefixIndex perm ix
        in case cmpNat (Proxy @p) (Proxy @n) of
          EQI -> astGatherKnobsR @p @(n - p) knobs
                                 (backpermutePrefixShape perm (shapeAst v)) v
                                 (vars, asts)
          LTI -> astGatherKnobsR @p @(n - p) knobs
                                 (backpermutePrefixShape perm (shapeAst v)) v
                                 (vars, asts)
          _ -> error "astTransposeAsGather: permutation longer than rank"
    Nothing -> error "astTransposeAsGather: impossible someNatVal error"

astTransposeAsGatherS
  :: forall perm sh s r p.
     (KnownShS perm, KnownShS sh, Sh.Rank perm <= Sh.Rank sh, p ~ Sh.Rank perm)
  => SimplifyKnobs -> AstShaped s r sh -> AstShaped s r (Sh.Permute perm sh)
{-# NOINLINE astTransposeAsGatherS #-}
astTransposeAsGatherS knobs v =
  withShapeP (drop (length (shapeT @perm))
                 $ shapeT @sh) $ \(Proxy @shd) ->
    gcastWith (unsafeCoerce Refl :: Sh.Drop p sh :~: shd) $
    withShapeP (take (length (shapeT @perm))
                   $ shapeT @sh) $ \(Proxy @shp) ->
      gcastWith (unsafeCoerce Refl :: Sh.Take p sh :~: shp) $
      withShapeP (backpermutePrefixList (shapeT @perm)
                                           (shapeT @shp)) $ \(Proxy @sh2) ->
        gcastWith (unsafeCoerce Refl
                   :: Sh.Permute perm (Sh.Take p sh) :~: sh2) $
        funToVarsIxS @sh2 $ \ (!vars, !ix) ->
          let asts :: AstIndexS (Sh.Take p sh)
              asts = ShapedList.permutePrefixIndex (shapeT @perm) ix
          in gcastWith (unsafeCoerce Refl
                        :: Sh.Permute perm sh :~: sh2 X.++ Sh.Drop p sh) $
             astGatherKnobsS @sh2 @p @sh knobs v (vars, asts)

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
  => SimplifyKnobs -> ShapeInt m -> AstRanked s r p -> AstRanked s r m
{-# NOINLINE astReshapeAsGather #-}
astReshapeAsGather knobs shOut v =
  funToVarsIx (lengthShape shOut) $ \ (!vars, !ix) ->
    let shIn = shapeAst v
        asts :: AstIndex p
        asts = let i = toLinearIdx @m @0 shOut ix
               in simplifyAstIndex $ fromLinearIdx shIn i
                    -- we generate these, so we simplify
    in astGatherKnobsR @m @0 knobs shOut v (vars, asts)

astReshapeAsGatherS
  :: forall sh sh2 r s. (KnownShS sh, KnownShS sh2, Sh.Size sh ~ Sh.Size sh2)
  => SimplifyKnobs -> AstShaped s r sh -> AstShaped s r sh2
{-# NOINLINE astReshapeAsGatherS #-}
astReshapeAsGatherS knobs v =
  gcastWith (unsafeCoerce Refl :: sh2 X.++ '[] :~: sh2) $
  funToVarsIxS @sh2 $ \ (!vars, !ix) ->
    let shIn = knownShS @sh
        shOut = knownShS @sh2
        asts :: AstIndexS sh
        asts = let i :: ShapedList.ShapedNat (Sh.Size sh2) AstInt
                   i = ShapedList.toLinearIdx @sh2 @'[] shOut ix
               in simplifyAstIndexS $ ShapedList.fromLinearIdx shIn i
                    -- we generate these, so we simplify
    in gcastWith (unsafeCoerce Refl :: Sh.Take (Sh.Rank sh) sh :~: sh) $
       gcastWith (unsafeCoerce Refl :: Sh.Drop (Sh.Rank sh) sh :~: '[]) $
       astGatherKnobsS @sh2 @(Sh.Rank sh) @sh knobs v (vars, asts)


-- * Permutation operations

normalizePermutation :: Permutation -> Permutation
normalizePermutation perm =
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
astNonIndexStep
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => AstRanked s r n -> AstRanked s r n
astNonIndexStep t = case t of
  Ast.AstVar{} -> t
  Ast.AstLet var u v -> astLet var u v
  Ast.AstShare{} -> t  -- TODO: error "astNonIndexStep: AstShare"
  Ast.AstCond a b c -> astCond a b c
  Ast.AstMinIndex{} -> t
  Ast.AstMaxIndex{} -> t
  Ast.AstFloor{} -> t
  Ast.AstIota -> t
  AstN1 opCode u ->
    case isRankedInt u of
      Just Refl -> contractAstNumOp1 opCode u
      _ -> t
  AstN2 opCode u v ->
    case isRankedInt u of
      Just Refl -> contractAstNumOp2 opCode u v
      _ -> t
  Ast.AstR1{} -> t
  Ast.AstR2{} -> t
  Ast.AstI2 opCode u v ->
    case isRankedInt u of
      Just Refl -> contractAstIntegralOp2 opCode u v
      _ -> t
  AstSumOfList args ->
    case isRankedInt t of
      Just Refl -> foldr1 contractAstPlusOp args
      _ -> t
  Ast.AstIndex{} -> t  -- was supposed to be *non*-index
  Ast.AstSum v -> astSum v
  Ast.AstScatter sh v (vars, ix) -> astScatter sh v (vars, ix)
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
  Ast.AstProject l p -> astProject l p
  Ast.AstLetHVectorIn vars u v -> astLetHVectorIn vars u v
  Ast.AstLetHFunIn var u v -> astLetHFunIn var u v
  Ast.AstRFromS v -> astRFromS v
  Ast.AstConstant{} -> t
  Ast.AstPrimalPart v -> astPrimalPart v  -- has to be done sooner or later
  Ast.AstDualPart v -> astDualPart v
  Ast.AstD{} -> t

astNonIndexStepS
  :: (KnownShS sh, GoodScalar r, AstSpan s)
  => AstShaped s r sh -> AstShaped s r sh
astNonIndexStepS t = case t of
  Ast.AstVarS{} -> t
  Ast.AstLetS var u v -> astLetS var u v
  Ast.AstShareS{} -> t  -- TODO: error "astNonIndexStepS: AstShareS"
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
  Ast.AstFromVectorS l -> astFromVectorS l
  Ast.AstReplicateS v -> astReplicateS v
  Ast.AstAppendS x y -> astAppendS x y
  Ast.AstSliceS @i @k v -> astSliceS @i @k v
  Ast.AstReverseS v -> astReverseS v
  Ast.AstTransposeS @perm v -> astTransposeS @perm v
  Ast.AstReshapeS v -> astReshapeS v
  Ast.AstBuild1S{} -> t
  Ast.AstGatherS @_ @p @sh1 v0 (ZS, ix) ->
    gcastWith (unsafeCoerce Refl :: sh1 :~: Sh.Take p sh1 X.++ Sh.Drop p sh1)
    $ Ast.AstIndexS v0 ix
  Ast.AstGatherS @sh2 @p @sh1 v0 (_ , ZIS) ->
    gcastWith (unsafeCoerce Refl :: Sh.Drop p sh1 :~: sh1) $
    astReplicateNS @sh2 @sh1 v0
  Ast.AstGatherS{} -> t  -- this is "index" enough
  Ast.AstCastS v -> astCastS v
  Ast.AstFromIntegralS v -> astFromIntegralS v
  AstConstS{} -> t
  Ast.AstProjectS l p -> astProjectS l p
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
astIndexR = astIndexKnobsR defaultKnobs

astIndexStep
  :: forall m n s r.
     (KnownNat m, KnownNat n, GoodScalar r, AstSpan s)
  => AstRanked s r (m + n) -> AstIndex m -> AstRanked s r n
astIndexStep v ix = astIndexKnobsR (defaultKnobs {knobStepOnly = True})
                                   (astNonIndexStep v)
                                   (simplifyAstIndex ix)

astIndexS
  :: forall sh1 sh2 s r.
     ( KnownShS sh1, KnownShS sh2, KnownShS (sh1 X.++ sh2)
     , GoodScalar r, AstSpan s )
  => AstShaped s r (sh1 X.++ sh2) -> AstIndexS sh1
  -> AstShaped s r sh2
astIndexS = astIndexKnobsS defaultKnobs

astIndexStepS
  :: forall sh1 sh2 s r.
     ( KnownShS sh1, KnownShS sh2, KnownShS (sh1 X.++ sh2)
     , GoodScalar r, AstSpan s )
  => AstShaped s r (sh1 X.++ sh2) -> AstIndexS sh1
  -> AstShaped s r sh2
astIndexStepS v ix = astIndexKnobsS (defaultKnobs {knobStepOnly = True})
                                    (astNonIndexStepS v)
                                    (simplifyAstIndexS ix)

-- If knobStepOnly is set, we reduce only as long as needed to reveal
-- a non-indexing constructor or one of the normal forms (one-element
-- indexing applied to AstFromVector or indexing
-- of a term with no possible occurrences of Int variables). Otherwise,
-- we simplify exhaustively.
--
-- The v0 term is already at least one step simplified,
-- either from full recursive simplification or from astIndexStep.
astIndexKnobsR
  :: forall m n s r.
     (KnownNat m, KnownNat n, GoodScalar r, AstSpan s)
  => SimplifyKnobs -> AstRanked s r (m + n) -> AstIndex m -> AstRanked s r n
astIndexKnobsR knobs (Ast.AstIndex v ix) ZIR =
  astIndexKnobsR knobs v ix  -- no non-indexing constructor yet revealed
astIndexKnobsR _ v0 ZIR = v0
astIndexKnobsR knobs v0 ix@(i1 :.: (rest1 :: AstIndex m1)) =
 let astIndexRec, astIndex
       :: forall m' n' s'. (KnownNat m', KnownNat n', AstSpan s')
       => AstRanked s' r (m' + n') -> AstIndex m' -> AstRanked s' r n'
     astIndexRec v2 ZIR = v2
     astIndexRec v2 ix2 = if knobStepOnly knobs
                          then Ast.AstIndex v2 ix2
                          else astIndexKnobsR knobs v2 ix2
     astIndex v2 ix2 = if knobStepOnly knobs
                       then astIndexKnobsR knobs
                                           (astNonIndexStep v2)
                                           (simplifyAstIndex ix2)
                       else astIndexKnobsR knobs v2 ix2
     astGather
       :: forall m' n' p'.
          (KnownNat m', KnownNat p', KnownNat n')
       => ShapeInt (m' + n') -> AstRanked s r (p' + n')
       -> (AstVarList m', AstIndex p')
       -> AstRanked s r (m' + n')
     astGather sh2 v2 (vars2, ix2) =
       if knobStepOnly knobs
       then astGatherKnobsR knobs
                            sh2 (astNonIndexStep v2)
                            (vars2, simplifyAstIndex ix2)
       else astGatherKnobsR knobs sh2 v2 (vars2, ix2)
 in case v0 of
  Ast.AstVar{} -> Ast.AstIndex v0 ix
  Ast.AstLet var u v -> astLet var u (astIndexRec v ix)
  Ast.AstShare{} -> Ast.AstIndex v0 ix  -- TODO: error "astIndexKnobsR: AstShare"
  Ast.AstCond b v w ->
    shareIx ix $ \ix2 -> astCond b (astIndexRec v ix2) (astIndexRec w ix2)
  Ast.AstMinIndex v -> Ast.AstMinIndex $ astIndexKnobsR knobs v ix
  Ast.AstMaxIndex v -> Ast.AstMaxIndex $ astIndexKnobsR knobs v ix
  Ast.AstFloor v -> Ast.AstFloor $ astIndexKnobsR knobs v ix
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
        else astReplicate0N (dropShape @m1 sh) 0
  -- AstScatter sh v (vars2, ZIR) ->
  --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZIR)
  Ast.AstScatter{} ->  -- normal form
    Ast.AstIndex v0 ix
  Ast.AstFromVector l | AstConst it <- i1 ->
    let i = fromIntegral $ OR.unScalar it
    in if 0 <= i && i < length l
       then astIndex (l V.! i) rest1
       else astReplicate0N (dropShape $ shapeAst v0) 0
  Ast.AstFromVector{} | ZIR <- rest1 ->  -- normal form
    Ast.AstIndex v0 ix
  Ast.AstFromVector l ->
    shareIx rest1 $ \ix2 ->
      Ast.AstIndex (astFromVector $ V.map (`astIndexRec` ix2) l)
                   (singletonIndex i1)
  Ast.AstReplicate k v | AstConst it <- i1 ->
    let i = fromIntegral $ OR.unScalar it
    in if 0 <= i && i < k
       then astIndex v rest1
       else astReplicate0N (dropShape $ shapeAst v) 0
{- TODO: this generalization of the above case slows down test 3nestedSumBuild1
   orders of magnitude
  Ast.AstReplicate k v ->
    let len = AstConst $ fromIntegral k
        zero = astReplicate0N (dropShape $ shapeAst v) 0
    in case simplifyAstBool $ Ast.AstB2 AndOp (Ast.AstRel LeqOp 0 i1)
                                              (Ast.AstRel LsOp i1 len) of
      AstBoolConst b -> if b then astIndex v rest1 else zero
      bExpr -> astCond bExpr (astIndex v rest1) zero -}
  Ast.AstReplicate _k v ->
    astIndex v rest1
  Ast.AstAppend u v ->
    let ulen = AstConst $ fromIntegral $ lengthAst u
        ix2 = simplifyAstInt (AstN2 MinusOp i1 ulen) :.: rest1
    in case simplifyAstBool $ Ast.AstRel LsOp i1 ulen of
      AstBoolConst b -> if b then astIndex u ix else astIndex v ix2
      bExpr -> astCond bExpr (astIndexRec u ix) (astIndexRec v ix2)
  Ast.AstSlice i _k v ->
    let ii = simplifyAstInt (i1 + fromIntegral i)
      -- we generate this index, so we simplify on the spot
    in astIndex v (ii :.: rest1)
  Ast.AstReverse v ->
    let iRev = simplifyAstInt (fromIntegral (lengthAst v - 1) - i1)
      -- we generate this index, so we simplify on the spot
    in astIndex v (iRev :.: rest1)
  Ast.AstTranspose perm v | valueOf @m >= length perm ->
    astIndex v (permutePrefixIndex perm ix)
  Ast.AstTranspose perm v ->
    astIndex (astTransposeAsGather knobs perm v) ix
  Ast.AstReshape sh v ->
    astIndex (astReshapeAsGather knobs sh v) ix
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
  Ast.AstCast t -> astCast $ astIndexKnobsR knobs t ix
  Ast.AstFromIntegral v -> astFromIntegral $ astIndexKnobsR knobs v ix
  AstConst t ->
    let unConst :: AstInt -> Maybe [OR.Array 0 Int64]
                -> Maybe [OR.Array 0 Int64]
        unConst (AstConst i) (Just l) = Just $ i : l
        unConst _ _ = Nothing
    in case foldr unConst (Just []) ix of
      Just ixInt -> AstConst $ tindexZR t $ listToIndex
                    $ map OR.unScalar ixInt
        -- TODO: we'd need mapM for Index to keep this rank-typed
      Nothing -> Ast.AstIndex v0 ix
  Ast.AstProject{} -> error "astIndexKnobsR: AstProject"
    {- The term should get simplified before this monstrosity kicks in:
    fun1DToAst (shapeAstHVector l) $ \ !vars !asts ->
      let lp = fromDynamicR (\sh -> astReplicate0N sh 0) (asts V.! p)
      in astLetHVectorIn vars l (astIndexRec lp ix) -}
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars l (astIndexRec v ix)
  Ast.AstLetHFunIn var f v ->
    astLetHFunIn var f (astIndexRec v ix)
  Ast.AstRFromS @sh t ->
    let (takeSh, dropSh) = splitAt (valueOf @m) (shapeT @sh)
    in withShapeP takeSh $ \(Proxy @p_take) ->
       withShapeP dropSh $ \(Proxy @p_drop) ->
       gcastWith (unsafeCoerce Refl :: sh :~: p_take X.++ p_drop) $
       gcastWith (unsafeCoerce Refl :: Sh.Rank p_drop :~: n) $
       astRFromS $ astIndexKnobsS @p_take @p_drop knobs
                                  t (ShapedList.listToIndex $ indexToList ix)
  Ast.AstConstant v -> Ast.AstConstant $ astIndex v ix
  Ast.AstPrimalPart{} -> Ast.AstIndex v0 ix  -- must be a NF
  Ast.AstDualPart{} -> Ast.AstIndex v0 ix
  Ast.AstD u u' ->
    shareIx ix $ \ix2 -> Ast.AstD (astIndexRec u ix2) (astIndexRec u' ix2)

astIndexKnobsS
  :: forall shm shn s r.
     ( KnownShS shm, KnownShS shn, KnownShS (shm X.++ shn)
     , GoodScalar r, AstSpan s )
  => SimplifyKnobs -> AstShaped s r (shm X.++ shn) -> AstIndexS shm
  -> AstShaped s r shn
astIndexKnobsS knobs (Ast.AstIndexS v ix) ZIS = astIndexKnobsS knobs v ix
astIndexKnobsS _ v0 ZIS = v0
astIndexKnobsS knobs v0 ix@((:.$) @in1 i1 (rest1 :: AstIndexS shm1)) | Dict <- sixKnown rest1 =
  let astIndexRec, astIndex
        :: forall shm' shn' s'.
           ( KnownShS shm', KnownShS shn', KnownShS (shm' X.++ shn')
           , AstSpan s' )
        => AstShaped s' r (shm' X.++ shn') -> AstIndexS shm'
        -> AstShaped s' r shn'
      astIndexRec v2 ZIS = v2
      astIndexRec v2 ix2 = if knobStepOnly knobs
                           then Ast.AstIndexS v2 ix2
                           else astIndexKnobsS knobs v2 ix2
      astIndex v2 ix2 = if knobStepOnly knobs
                        then astIndexKnobsS knobs
                                            (astNonIndexStepS v2)
                                            (simplifyAstIndexS ix2)
                        else astIndexKnobsS knobs v2 ix2
      astGather
        :: forall shm' shn' p'.
           ( KnownShS shm', KnownShS shn'
           , KnownShS (Sh.Take p' shm'), KnownShS (Sh.Drop p' shm') )
        => AstShaped s r shm'
        -> (AstVarListS shn', AstIndexS (Sh.Take p' shm'))
        -> AstShaped s r (shn' X.++ Sh.Drop p' shm')
      astGather v2 (vars2, ix2) =
        if knobStepOnly knobs
        then astGatherKnobsS knobs
                             (astNonIndexStepS v2)
                             (vars2, simplifyAstIndexS ix2)
        else astGatherKnobsS knobs v2 (vars2, ix2)
 in case v0 of
  Ast.AstVarS{} -> Ast.AstIndexS v0 ix
  Ast.AstLetS var u v -> astLetS var u (astIndexRec v ix)
  Ast.AstShareS{} -> Ast.AstIndexS v0 ix  -- TODO: error "astIndexKnobsRS: AstShareS"
  Ast.AstCondS b v w ->
    shareIxS ix $ \ix2 -> astCondS b (astIndexRec v ix2) (astIndexRec w ix2)
  Ast.AstMinIndexS @shz @n1 v ->
    withShapeP (drop 1 (shapeT @shn)
                   ++ [last (shapeT @shz)]) $ \(Proxy @shd) ->
      gcastWith (unsafeCoerce Refl
                 :: Sh.Drop 1 shn X.++ '[Sh.Last shz] :~: shd) $
      withSNat (shapeT @shn !! 0) $ \(SNat @i0shn) ->
        gcastWith (unsafeCoerce Refl :: Sh.Index shn 0 :~: i0shn) $
        gcastWith (unsafeCoerce Refl
                   :: Sh.Index shn 0 ': Sh.Drop 1 shn :~: shn) $
        gcastWith (unsafeCoerce Refl
                   :: Sh.Init (shn X.++ '[Sh.Last shz]) :~: shn) $
        gcastWith (unsafeCoerce Refl
                   :: shm X.++ (shn X.++ '[Sh.Last shz]) :~: n1 ': shz) $
        Ast.AstMinIndexS @(Sh.Drop 1 shn X.++ '[Sh.Last shz]) @(Sh.Index shn 0)
        $ astIndexKnobsS @shm @(shn X.++ '[Sh.Last shz]) knobs v ix
  Ast.AstMaxIndexS @shz @n1 v ->
    withShapeP (drop 1 (shapeT @shn)
                   ++ [last (shapeT @shz)]) $ \(Proxy @shd) ->
      gcastWith (unsafeCoerce Refl
                 :: Sh.Drop 1 shn X.++ '[Sh.Last shz] :~: shd) $
      withSNat (shapeT @shn !! 0) $ \(SNat @i0shn) ->
        gcastWith (unsafeCoerce Refl :: Sh.Index shn 0 :~: i0shn) $
        gcastWith (unsafeCoerce Refl
                   :: Sh.Index shn 0 ': Sh.Drop 1 shn :~: shn) $
        gcastWith (unsafeCoerce Refl
                   :: Sh.Init (shn X.++ '[Sh.Last shz]) :~: shn) $
        gcastWith (unsafeCoerce Refl
                   :: shm X.++ (shn X.++ '[Sh.Last shz]) :~: n1 ': shz) $
        Ast.AstMaxIndexS @(Sh.Drop 1 shn X.++ '[Sh.Last shz]) @(Sh.Index shn 0)
        $ astIndexKnobsS @shm @(shn X.++ '[Sh.Last shz]) knobs v ix
  Ast.AstFloorS v -> Ast.AstFloorS $ astIndexKnobsS knobs v ix
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
               :: (sh4 X.++ shm) X.++ shn :~: sh4 X.++ (shm X.++ shn)) $
    withShapeP (shapeT @sh4 ++ shapeT @shm) $ \(Proxy @sh41) ->
      gcastWith (unsafeCoerce Refl :: sh4 X.++ shm :~: sh41) $
      astIndexS v (ShapedList.appendIndex ix2 ix)
  Ast.AstSumS @n1 v ->
    let perm3 = backpermCycle $ length (shapeT @shm) + 1
    in withShapeP (shapeT @shm
                      ++ (valueOf @n1 : shapeT @shn)) $ \(Proxy @sm1n) ->
      gcastWith (unsafeCoerce Refl :: shm X.++ (n1 : shn) :~: sm1n) $
      withSNat (1 + length (shapeT @shn)
                + length (shapeT @shm)) $ \(SNat @r1mn) ->
        gcastWith (unsafeCoerce Refl :: Sh.Rank (n1 : shm X.++ shn) :~: r1mn) $
        withShapeP perm3 $ \(Proxy @perm3P) ->
          gcastWith (unsafeCoerce Refl
                     :: Compare (OS.Rank perm3P) (Sh.Rank (n1 : shm X.++ shn))
                        :~: LT) $
          gcastWith (unsafeCoerce Refl
                     :: Sh.Permute perm3P (n1 : (shm X.++ shn))
                        :~: shm X.++ (n1 : shn)) $
          trustMeThisIsAPermutation @perm3P $
          astSumS $ astIndex @shm @(n1 : shn)
                             (astTransposeS @perm3P @(n1 : shm X.++ shn) v)
                             ix
-- TODO:
--  Ast.AstScatterS @sh2 @p7 @sh7
--                  v (vars, AstIntVar var5 ::$ (ix2 :: AstIndexS p71))
--    | AstIntVar var6 <- i1, var6 == var5 ->
--        gcastWith (unsafeCoerce Refl
--                   :: shm1 X.++ shn :~: p71 X.++ Sh.Drop p7 sh7) $
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
  Ast.AstFromVectorS l | AstConst it <- i1 ->
    let i = fromIntegral $ OR.unScalar it
    in if 0 <= i && i < length l
       then astIndex (l V.! i) rest1
       else {-srepl-} 0
  Ast.AstFromVectorS{} | ZIS <- rest1 ->  -- normal form
    Ast.AstIndexS v0 ix
  Ast.AstFromVectorS l ->
    shareIxS rest1 $ \ix2 ->
      Ast.AstIndexS @'[in1] @shn (astFromVectorS $ V.map (`astIndexRec` ix2) l)
                    (ShapedList.singletonIndex i1)
  Ast.AstReplicateS v ->
    astIndex v rest1
  Ast.AstAppendS @_ @m u v ->
    let ulen = AstConst $ fromIntegral (valueOf @m :: Int)
        ix1 = i1 :.$ rest1
        ix2 = simplifyAstInt (AstN2 MinusOp i1 ulen) :.$ rest1
    in case simplifyAstBool $ Ast.AstRel LsOp i1 ulen of
      AstBoolConst b -> if b then astIndex u ix1 else astIndex v ix2
      bExpr -> astCondS bExpr (astIndexRec u ix1) (astIndexRec v ix2)
  Ast.AstSliceS @i v ->
    let ii = simplifyAstInt (i1 + fromIntegral (valueOf @i :: Int))
      -- we generate this index, so we simplify on the spot
    in astIndex v (ii :.$ rest1)
  Ast.AstReverseS v ->
    let iRev = simplifyAstInt (fromIntegral (valueOf @in1 - 1 :: Int) - i1)
      -- we generate this index, so we simplify on the spot
    in astIndex v (iRev :.$ rest1)
  Ast.AstTransposeS @perm @sh2 v
    | length (shapeT @shm) >= length (shapeT @perm) ->
      withShapeP
        (permutePrefixList (shapeT @perm)
                           (shapeT @shm)) $ \(Proxy @shmPerm) ->
          gcastWith (unsafeCoerce Refl :: shm :~: Sh.Permute perm shmPerm) $
          let ix2 :: AstIndexS shmPerm =
                ShapedList.permutePrefixIndexT @perm ix
          in gcastWith (unsafeCoerce Refl :: sh2 :~: shmPerm X.++ shn) $
             astIndex @shmPerm v ix2
  Ast.AstTransposeS @perm v ->
    astIndex (astTransposeAsGatherS @perm knobs v) ix
  Ast.AstReshapeS v ->
    astIndex (astReshapeAsGatherS knobs v) ix
  Ast.AstBuild1S (var2, v) ->
    withListSh (Proxy @(shm1 X.++ shn)) $ \_ ->
      astIndex (astSFromR @(shm1 X.++ shn) $ astLet var2 i1 $ astRFromS v)
               rest1
      -- this uses astLet, because the index integers are ranked
  Ast.AstGatherS @_ @p @sh v (ZS, ix2) ->
    withShapeP (shapeT @(Sh.Take p sh) ++ shapeT @shm)
    $ \(Proxy @sh1n) ->
      gcastWith (unsafeCoerce Refl :: (Sh.Take p sh X.++ shm :~: sh1n)) $
      gcastWith (unsafeCoerce Refl :: Sh.Take p sh X.++ shm X.++ shn :~: sh) $
        -- TODO: why is this needed? if it's true (it is), GHC should know it
      astIndex v (ShapedList.appendIndex ix2 ix)
  Ast.AstGatherS v (Const var2 ::$ (vars :: AstVarListS shm71), ix2) | Dict <- slistKnown vars ->
    withListSh (Proxy @shn) $ \_ ->
      withShapeP (shapeT @shm1 ++ shapeT @shn) $ \(Proxy @sh1n) ->
        gcastWith (unsafeCoerce Refl :: shm1 X.++ shn :~: sh1n) $
        let w :: AstShaped s r (shm1 X.++ shn)
            w = astGather v (vars, ix2)
        in astSFromR $ astLet var2 i1 $ astRFromS $ astIndexS @shm1 @shn w rest1
      -- this uses astLet, because the index integers are ranked
  Ast.AstCastS t -> astCastS $ astIndexKnobsS knobs t ix
  Ast.AstFromIntegralS v -> astFromIntegralS $ astIndexKnobsS knobs v ix
  AstConstS t ->
    let unConst :: AstInt -> Maybe [OR.Array 0 Int64]
                -> Maybe [OR.Array 0 Int64]
        unConst (AstConst i) (Just l) = Just $ i : l
        unConst _ _ = Nothing
    in case foldr unConst (Just []) ix of
      Just ixInt -> AstConstS $ FlipS $ tindexZS (runFlipS t)
                    $ ShapedList.listToIndex @shm $ map OR.unScalar ixInt
        -- TODO: we'd need mapM for Index to keep this rank-typed
      Nothing -> Ast.AstIndexS v0 ix
  Ast.AstProjectS{} -> error "astIndexKnobsRS: AstProjectsS"
    {- The term should get simplified before this monstrosity kicks in:
    fun1DToAst (shapeAstHVector l) $ \ !vars !asts ->
      let lp = fromDynamicS (asts V.! p)
      in astLetHVectorInS vars l (astIndexRec lp ix) -}
  Ast.AstLetHVectorInS vars l v ->
    astLetHVectorInS vars l (astIndexRec v ix)
  Ast.AstLetHFunInS var f v ->
    astLetHFunInS var f (astIndexRec v ix)
  Ast.AstSFromR @sh t ->
    withListSh (Proxy @shn) $ \_ ->
      gcastWith (unsafeCoerce Refl
                 :: Sh.Rank shm + Sh.Rank shn :~: Sh.Rank (shm Sh.++ shn)) $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Rank shm + Sh.Rank shn :~: Sh.Rank (shm X.++ shn)) $
                      -- reversing this equality causes "Could not deduce
                      -- ‘KnownNat (OS.Rank sh1)’ error, but this is
                      -- probably ~fine and maybe caused by KnownNat.Solver
      astSFromR $ astIndexKnobsR knobs t (ShapedList.shapedToIndex ix)
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
  let shareI :: AstInt -> IO (Maybe (IntVarName, AstInt), AstInt)
      shareI i | astIsSmall True i = return (Nothing, i)
      shareI i = funToAstIntVarIO $ \ (!varFresh, !astVarFresh) ->
                   (Just (varFresh, i), astVarFresh)
  (bindings, ix2) <- mapAndUnzipM shareI (indexToList ix)
  return $! foldr (uncurry Ast.AstLet) (f $ listToIndex ix2)
                                       (catMaybes bindings)

shareIxS :: -- (KnownShS shn, KnownShS shm)
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
astGatherR = astGatherKnobsR defaultKnobs

astGatherS
  :: forall sh2 p sh s r.
     ( KnownShS sh, KnownShS sh2
     , KnownShS (Sh.Take p sh), KnownShS (Sh.Drop p sh) )
  => AstShaped s r sh
  -> (AstVarListS sh2, AstIndexS (Sh.Take p sh))
  -> AstShaped s r (sh2 X.++ Sh.Drop p sh)
astGatherS = astGatherKnobsS defaultKnobs

astGatherStep
  :: forall m n p s r.
     (KnownNat m, KnownNat p, KnownNat n, GoodScalar r, AstSpan s)
  => ShapeInt (m + n) -> AstRanked s r (p + n) -> (AstVarList m, AstIndex p)
  -> AstRanked s r (m + n)
astGatherStep sh v (vars, ix) =
  astGatherKnobsR (defaultKnobs {knobStepOnly = True})
                  sh (astNonIndexStep v)
                  (vars, simplifyAstIndex ix)

astGatherStepS
  :: forall sh2 p sh s r.
     ( KnownShS sh, KnownShS sh2, GoodScalar r, AstSpan s
     , KnownShS (Sh.Take p sh), KnownShS (Sh.Drop p sh) )
  => AstShaped s r sh
  -> (AstVarListS sh2, AstIndexS (Sh.Take p sh))
  -> AstShaped s r (sh2 X.++ Sh.Drop p sh)
-- TODO: this probably needs an extra condition similar to kN == vkN below
--astGatherStepS v (AstVarName varId ::$ ZSS, AstIntVarS varId2 :.$ ZIS)
--  | varId == varId2 = ...
astGatherStepS v (vars, ix) =
  astGatherKnobsS (defaultKnobs {knobStepOnly = True})
                  (astNonIndexStepS v)
                  (vars, simplifyAstIndexS ix)

-- Assumption: vars0 don't not occur in v0. The assumption only holds
-- when newly generated variables are fresh, which is the case as long
-- as resetVarCounter is not used. The assumption makes it easier to spot
-- bugs or corruption, hence we assert it in the code below.
--
-- The v0 term is already at least one step simplified,
-- either from full recursive simplification or from astGatherStep.
astGatherKnobsR
  :: forall m n p s r.
     (KnownNat m, KnownNat p, KnownNat n, GoodScalar r, AstSpan s)
  => SimplifyKnobs -> ShapeInt (m + n) -> AstRanked s r (p + n)
  -> (AstVarList m, AstIndex p)
  -> AstRanked s r (m + n)
astGatherKnobsR knobs sh0 v0 (vars0, ix0) =
  case (sh0, (vars0, ix0)) of
    _ | any (`varNameInAst` v0) vars0 ->
      error $ "astGather: gather vars in v0: "
              ++ show (vars0, v0)
    (_, (ZR, _)) -> astIndex v0 ix0
    (sh, (_, ZIR)) -> if knobExpand knobs
                      then Ast.AstGather sh0 v0 (vars0, ix0)
                      else astReplicateN sh v0
    (k :$: sh', (AstVarName varId ::: vars, i1 :.: rest1)) ->
      if | not (any (`varNameInAst` i1) vars0) ->
           astGatherKnobsR knobs sh0 (astIndex v0 (i1 :.: ZIR))
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
           -> astGatherKnobsR knobs sh0 v0 (varsN, restN)
         | varInIndex varId ix0 ->
           astGatherCase sh0 v0 (vars0, ix0)
         | otherwise ->
           if knobExpand knobs
           then Ast.AstGather sh0 v0 (vars0, ix0)
           else case knownShR sh' of
             Dict ->astReplicate k (astGatherKnobsR knobs sh' v0 (vars, ix0))
       where
        (restN, iN) = unsnocIndex1 ix0
        (varsN, varN) = unsnocSized1 vars0
    _ ->
      error "astGather: impossible pattern needlessly required"
 where
  astIndex :: forall m' n' s'. (KnownNat m', KnownNat n', AstSpan s')
           => AstRanked s' r (m' + n') -> AstIndex m' -> AstRanked s' r n'
  astIndex v2 ix2 = if knobStepOnly knobs
                    then astIndexKnobsR knobs
                                        (astNonIndexStep v2)
                                        (simplifyAstIndex ix2)
                    else astIndexKnobsR knobs v2 ix2
  astGatherRec, astGather
    :: forall m' n' p' s' r'.
       (KnownNat m', KnownNat p', KnownNat n', AstSpan s', GoodScalar r')
    => ShapeInt (m' + n') -> AstRanked s' r' (p' + n')
    -> (AstVarList m', AstIndex p')
    -> AstRanked s' r' (m' + n')
  astGatherRec sh2 v2 (vars2, ix2) =
    if knobStepOnly knobs
    then Ast.AstGather sh2 v2 (vars2, ix2)
    else astGatherKnobsR knobs sh2 v2 (vars2, ix2)
  astGather sh2 v2 (vars2, ix2) =
    if knobStepOnly knobs
    then astGatherKnobsR knobs
                         sh2 (astNonIndexStep v2)
                         (vars2, simplifyAstIndex ix2)
    else astGatherKnobsR knobs sh2 v2 (vars2, ix2)
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
    Ast.AstShare{} -> error "astGatherCase: AstShare"
    Ast.AstCond b v w -> astCond b (astGather sh4 v (vars4, ix4))
                                   (astGather sh4 w (vars4, ix4))
    Ast.AstMinIndex v ->
      Ast.AstMinIndex
      $ astGatherKnobsR knobs
          (sh4 `appendShape` singletonShape (lastShape (shapeAst v)))
          v (vars4, ix4)
    Ast.AstMaxIndex v ->
      Ast.AstMaxIndex
      $ astGatherKnobsR knobs
          (sh4 `appendShape` singletonShape (lastShape (shapeAst v)))
          v (vars4, ix4)
    Ast.AstFloor v ->
      Ast.AstFloor
      $ astGatherKnobsR knobs sh4 v (vars4, ix4)
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
      (Ast.AstFromVector{}, i2 :.: ZIR) -> astGather sh4 v2 (vars4, i2 :.: ix4)
      _ ->  -- AstVar, AstConst
        Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstSum v ->
      let perm3 = backpermCycle $ valueOf @p' + 1
          perm4 = permCycle $ valueOf @m' + 1
          (sh41, sh42) = splitAt_Shape @m' sh4
          sh5 = appendShape sh41 (lengthAst v :$: sh42)
          innerGather = astGather sh5 (astTranspose perm3 v) (vars4, ix4)
      in if not (knobExpand knobs) || length perm4 <= valueOf @m'
         then astSum $ astTranspose perm4 innerGather
         else astSum $ astTransposeAsGather knobs perm4 innerGather
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
          else astReplicate0N sh4 0
    Ast.AstScatter{} ->  -- normal form
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstFromVector l | AstConst it <- i4 ->
      let i = fromIntegral $ OR.unScalar it
      in if 0 <= i && i < length l
         then astGather sh4 (l V.! i) (vars4, rest4)
         else astReplicate0N sh4 0
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
    Ast.AstReplicate k v | AstConst it <- i4 ->
      let i = fromIntegral $ OR.unScalar it
      in if 0 <= i && i < k
         then astGather sh4 v (vars4, rest4)
         else astReplicate0N sh4 0
    Ast.AstReplicate _k v -> astGather sh4 v (vars4, rest4)
    Ast.AstAppend u v ->
      let ulen = AstConst $ fromIntegral $ lengthAst u
          iu = simplifyAstInt (AstN2 MinusOp i4 ulen)
      in case simplifyAstBool $ Ast.AstRel LsOp i4 ulen of
        AstBoolConst b -> if b
                          then astGather sh4 u (vars4, i4 :.: rest4)
                          else astGather sh4 v (vars4, iu :.: rest4)
        bExpr ->
          funToVarsIx (valueOf @m') $ \ (!varsFresh, !ixFresh) ->
            let u2 = astGatherRec sh4 u (vars4, i4 :.: rest4)
                v2 = astGatherRec sh4 v (vars4, iu :.: rest4)
                -- This subst doesn't break sharing because it's a rename.
                subst i =
                  foldr (uncurry substituteAstBool) i
                        (zipSized (fmap (SubstitutionPayloadRanked
                                           @PrimalSpan @Int64)
                                   $ indexToSized ixFresh) vars4)
                bExpr5 = subst bExpr
            in astGather sh4 (astFromVector $ V.fromList [u2, v2])
                             (varsFresh, astCond bExpr5 0 1 :.: ixFresh)
    Ast.AstSlice i _k v ->
      let ii = simplifyAstInt (i4 + fromIntegral i)
        -- we generate this index, so we simplify on the spot
      in astGather sh4 v (vars4, ii :.: rest4)
    Ast.AstReverse v ->
      let iRev = simplifyAstInt (fromIntegral (lengthAst v - 1) - i4)
        -- we generate this index, so we simplify on the spot
      in astGather sh4 v (vars4, iRev :.: rest4)
    Ast.AstTranspose perm v | valueOf @p' >= length perm ->
      astGather sh4 v (vars4, permutePrefixIndex perm ix4)
    Ast.AstTranspose perm v ->
      if knobExpand knobs
      then astGather sh4 (astTransposeAsGather knobs perm v) (vars4, ix4)
      else Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstReshape sh v ->
      if knobExpand knobs
      then astGather sh4 (astReshapeAsGather knobs sh v) (vars4, ix4)
      else Ast.AstGather sh4 v4 (vars4, ix4)
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
            simplifyAstInt  -- we generate the index, so we simplify on the spot
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
    Ast.AstProject{} ->  -- most likely reduced before it gets there
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstLetHVectorIn vars l v ->
      astLetHVectorIn vars l (astGatherCase sh4 v (vars4, ix4))
    Ast.AstLetHFunIn var f v ->
      astLetHFunIn var f (astGatherCase sh4 v (vars4, ix4))
    Ast.AstRFromS{} {- @sh v -} -> Ast.AstGather sh4 v4 (vars4, ix4)
      -- TODO: this is broken
      {-
      let (takeSh, dropSh) = splitAt (valueOf @p') (shapeT @sh)
      in withShapeP takeSh $ \(Proxy @p_take) ->
         withShapeP dropSh $ \(Proxy @p_drop) ->
         gcastWith (unsafeCoerce Refl :: sh :~: p_take X.++ p_drop) $
         gcastWith (unsafeCoerce Refl :: p_take :~: Sh.Take p' sh) $
         gcastWith (unsafeCoerce Refl :: p_drop :~: Sh.Drop p' sh) $
         gcastWith (unsafeCoerce Refl :: Sh.Rank sh :~: p' + n') $
         astRFromS $ astGatherStepS @_ @p' @sh v
                     ( ShapedList.listToSized $ sizedToList vars4
                     , ShapedList.listToSized $ indexToList ix4 ) -}
    Ast.AstConstant v -> Ast.AstConstant $ astGather sh4 v (vars4, ix4)
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

astGatherKnobsS
  :: forall sh2 p sh s r.
     ( KnownShS sh, KnownShS sh2
     , KnownShS (Sh.Take p sh), KnownShS (Sh.Drop p sh) )
  => SimplifyKnobs -> AstShaped s r sh
  -> (AstVarListS sh2, AstIndexS (Sh.Take p sh))
  -> AstShaped s r (sh2 X.++ Sh.Drop p sh)
astGatherKnobsS _ v (vars, ix) = Ast.AstGatherS v (vars, ix)  -- TODO

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
astLet var u v = Ast.AstLet var u v

-- A special variant to bind integer expressions inside indexes.
-- It check if the bound variables appears in the body at all.
-- Normally, that's asymptotically worse than doing this
-- in a global inlining pass, but we assume indexes expressions
-- are short and we need them simple ASAP.
astLetInt :: IntVarName -> AstInt -> AstInt -> AstInt
astLetInt var u v | var `varNameInAst` v = astLet var u v
astLetInt _ _ v = v

-- Inlining works for this let constructor, because it has just one variable,
-- unlike astLetHVectorIn, etc., so we don't try to eliminate it.
astLetS :: forall sh1 sh2 r r2 s s2.
           ( KnownShS sh1, KnownShS sh2, GoodScalar r, GoodScalar r2
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
astLetS var u v = Ast.AstLetS var u v

astCond :: AstBool -> AstRanked s r n -> AstRanked s r n -> AstRanked s r n
astCond (AstBoolConst b) v w = if b then v else w
astCond b (Ast.AstConstant v) (Ast.AstConstant w) =
  Ast.AstConstant $ Ast.AstCond b v w
astCond b v w = Ast.AstCond b v w

astCondS :: AstBool -> AstShaped s r sh -> AstShaped s r sh -> AstShaped s r sh
astCondS (AstBoolConst b) v w = if b then v else w
astCondS b (Ast.AstConstantS v) (Ast.AstConstantS w) =
  Ast.AstConstantS $ Ast.AstCondS b v w
astCondS b v w = Ast.AstCondS b v w

astSumOfList :: (KnownNat n, GoodScalar r, AstSpan s)
             => [AstRanked s r n] -> AstRanked s r n
astSumOfList = foldr1 (+)  -- @sum@ breaks and also reverse order

astSumOfListS :: (KnownShS sh, GoodScalar r, AstSpan s)
              => [AstShaped s r sh] -> AstShaped s r sh
astSumOfListS = foldr1 (+)  -- @sum@ reverses order

astSum :: (KnownNat n, GoodScalar r, AstSpan s)
       => AstRanked s r (1 + n) -> AstRanked s r n
astSum t0 = case shapeAst t0 of
  0 :$: rest -> astReplicate0N rest 0
--  1 :$: rest -> astReshape rest t0  -- TODO: slows down the CNNO test
  _ -> case t0 of
    -- Ast.AstLet var u v -> astLet var u (astSum v)
    -- this is problematic, because it keeps huge tensors alive for longer
    Ast.AstScatter (_ :$: sh) v (vars, _ :.: ix) -> astScatter sh v (vars, ix)
    Ast.AstFromVector l -> astSumOfList $ V.toList l
    Ast.AstReplicate k v -> v * astReplicate0N (shapeAst v) (fromIntegral k)
    Ast.AstSlice _i 0 v -> astReplicate0N (tailShape $ shapeAst v) 0
    Ast.AstSlice i 1 v -> astIndexR v (fromIntegral i :.: ZIR)
    Ast.AstReverse v -> astSum v
    AstConst t -> AstConst $ tsumR t
    Ast.AstConstant v -> Ast.AstConstant $ astSum v
    _ -> Ast.AstSum t0

astSumS :: forall n sh r s. (KnownNat n, KnownShS sh, GoodScalar r, AstSpan s)
        => AstShaped s r (n ': sh) -> AstShaped s r sh
astSumS t0 = case sameNat (Proxy @n) (Proxy @0) of
 Just Refl -> {-srepl-} 0
 _ -> case sameNat (Proxy @n) (Proxy @1) of
  Just Refl -> astReshapeS t0
  _ -> case t0 of
    -- Ast.AstLetS var u v -> astLetS var u (astSumS v)
    Ast.AstScatterS @sh2 @p v (vars, _ :.$ ix) | Dict <- sixKnown ix ->
      gcastWith (unsafeCoerce Refl
                 :: Sh.Drop p (n : sh) :~: Sh.Drop (p - 1) sh) $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Drop 1 (Sh.Take p (n : sh)) :~: Sh.Take (p - 1) sh) $
      astScatterS @sh2 @(p - 1) @sh v (vars, ix)
    Ast.AstFromVectorS l -> astSumOfListS $ V.toList l
    Ast.AstReplicateS @k v -> v * astReplicate0NS (valueOf @k)
    Ast.AstSliceS @i @k _v | Just Refl <- sameNat (Proxy @k) (Proxy @0) -> {-srepl-} 0
    Ast.AstSliceS @i @k v | Just Refl <- sameNat (Proxy @k) (Proxy @1) ->
      astIndexS v (valueOf @i :.$ ZIS)
    Ast.AstReverseS v -> astSumS v
    AstConstS t -> AstConstS $ FlipS $ tsumS $ runFlipS t
    Ast.AstConstantS v -> Ast.AstConstantS $ astSumS v
    _ -> Ast.AstSumS t0

-- TODO: fuse scatters, scatter and sum, perhaps more (fromList?)
astScatter :: forall m n p s r.
              (GoodScalar r, KnownNat m, KnownNat n, KnownNat p, AstSpan s)
           => ShapeInt (p + n) -> AstRanked s r (m + n)
           -> (AstVarList m, AstIndex p)
           -> AstRanked s r (p + n)
astScatter _sh v (ZR, ZIR) = v
astScatter sh@(k :$: _) _v (_vars, AstConst it :.: _ix)
  | let i = fromIntegral $ OR.unScalar it
  , not (0 <= i && i < k) =
      astReplicate0N sh 0
-- else update (rzero sh 0) [AstConst it] (astScatter ...)
astScatter sh v (AstVarName varId ::: vars, ix) | not $ varId `varInIndex` ix =
  astScatter sh (astSum v) (vars, ix)
-- astScatter sh v (ZR, ix) = update (rzero sh 0) ix v
astScatter sh (Ast.AstConstant v) (vars, ix) =
  Ast.AstConstant $ astScatter sh v (vars, ix)
astScatter sh v (vars, ix) = Ast.AstScatter sh v (vars, ix)

astScatterS :: forall sh2 p sh s r.
               ( KnownShS sh2, KnownShS sh
               , KnownShS (Sh.Take p sh), KnownShS (Sh.Drop p sh)
               , KnownShS (sh2 X.++ Sh.Drop p sh), GoodScalar r, AstSpan s )
            => AstShaped s r (sh2 X.++ Sh.Drop p sh)
            -> (AstVarListS sh2, AstIndexS (Sh.Take p sh))
            -> AstShaped s r sh
astScatterS v (ZS, ZIS) =
  gcastWith (unsafeCoerce Refl
             :: Sh.Take p sh X.++ Sh.Drop p sh :~: sh)
  v
astScatterS v (Const (AstVarName varId) ::$ (vars :: AstVarListS sh3), ix)
  | not $ varId `varInIndexS` ix
  , Dict <- slistKnown vars =
    withShapeP (shapeT @sh3
                ++ (shapeT @(Sh.Drop p sh))) $ \(Proxy @sh4) ->
      gcastWith (unsafeCoerce Refl :: sh3 X.++ Sh.Drop p sh :~: sh4) $
      astScatterS @sh3 @p @sh (astSumS v) (vars, ix)
-- astScatterS v (ZR, ix) = update (rzero sh 0) ix v
astScatterS (Ast.AstConstantS v) (vars, ix) =
  Ast.AstConstantS $ astScatterS v (vars, ix)
astScatterS v (vars, ix) = Ast.AstScatterS v (vars, ix)

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
                  (KnownNat n, KnownShS sh, GoodScalar r, AstSpan s)
               => Data.Vector.Vector (AstShaped s r sh)
               -> AstShaped s r (n ': sh)
astFromVectorS v | V.length v == 1 = astReplicateS (v V.! 0)
astFromVectorS l | Just Refl <- sameAstSpan @s @PrimalSpan =
  let unConst :: AstShaped PrimalSpan r sh -> Maybe (OS.Array sh r)
      unConst (AstConstS t) = Just $ runFlipS t
      unConst _ = Nothing
  in case V.mapM unConst l of
    Just l3 -> AstConstS $ FlipS $ tfromVectorS l3
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
                 (KnownNat n, KnownShS sh, GoodScalar r, AstSpan s)
              => AstShaped s r sh -> AstShaped s r (n ': sh)
astReplicateS = \case
  Ast.AstTransposeS @perm @sh1 v ->
    let zsuccPerm = 0 : map succ (shapeT @perm)
    in withShapeP zsuccPerm $ \(Proxy @zsuccP) ->
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
  let go :: ShapeInt n' -> AstRanked s r (n' + p)
      go ZSR = v
      go (k :$: sh2) | Dict <- knownShR sh2 = astReplicate k $ go sh2
  in go (takeShape sh)

astReplicateNS :: forall shn shp s r.
                  (KnownShS shn, KnownShS shp, GoodScalar r, AstSpan s)
               => AstShaped s r shp -> AstShaped s r (shn X.++ shp)
astReplicateNS v =
  let go :: ShS shn' -> AstShaped s r (shn' X.++ shp)
      go ZSS = v
      go ((:$$) @k @shn2 SNat shn2) | Dict <- sshapeKnown shn2 =
        withShapeP (shapeT @shn2 ++ shapeT @shp) $ \(Proxy @sh) ->
          gcastWith (unsafeCoerce Refl :: sh :~: shn2 X.++ shp) $
          astReplicateS @k $ go shn2
  in go (knownShS @shn)

astReplicate0N :: forall n s r. (GoodScalar r, AstSpan s)
               => ShapeInt n -> AstRanked s r 0 -> AstRanked s r n
astReplicate0N sh =
  let go :: ShapeInt n' -> AstRanked s r 0 -> AstRanked s r n'
      go ZSR v = v
      go (k :$: sh') v | Dict <- knownShR sh' = astReplicate k $ go sh' v
  in go sh

astReplicate0NS :: forall shn s r. (KnownShS shn, GoodScalar r, AstSpan s)
                => AstShaped s r '[] -> AstShaped s r shn
astReplicate0NS =
  let go :: ShS sh' -> AstShaped s r '[] -> AstShaped s r sh'
      go ZSS v = v
      go ((:$$) SNat sh') v | Dict <- sshapeKnown sh' = astReplicateS $ go sh' v
  in go (knownShS @shn)

astAppend :: (KnownNat n, GoodScalar r, AstSpan s)
          => AstRanked s r (1 + n) -> AstRanked s r (1 + n)
          -> AstRanked s r (1 + n)
astAppend (AstConst u) (AstConst v) = AstConst $ tappendR u v
astAppend (Ast.AstConstant u) (Ast.AstConstant v) =
  Ast.AstConstant $ astAppend u v
astAppend (Ast.AstFromVector l1) (Ast.AstFromVector l2) =
  astFromVector $ l1 V.++ l2
astAppend u v = Ast.AstAppend u v

astAppendS :: (KnownNat m, KnownNat n, KnownShS sh, GoodScalar r, AstSpan s)
           => AstShaped s r (m ': sh) -> AstShaped s r (n ': sh)
           -> AstShaped s r ((m + n) ': sh)
astAppendS (AstConstS u) (AstConstS v) = AstConstS $ FlipS $ tappendS (runFlipS u) (runFlipS v)
astAppendS (Ast.AstConstantS u) (Ast.AstConstantS v) =
  Ast.AstConstantS $ astAppendS u v
astAppendS (Ast.AstFromVectorS l1) (Ast.AstFromVectorS l2) =
  astFromVectorS $ l1 V.++ l2
astAppendS u v = Ast.AstAppendS u v

astSlice :: forall k s r. (KnownNat k, GoodScalar r, AstSpan s)
         => Int -> Int -> AstRanked s r (1 + k) -> AstRanked s r (1 + k)
astSlice i n (AstConst t) = AstConst $ tsliceR i n t
astSlice i n (Ast.AstConstant v) = Ast.AstConstant $ astSlice i n v
astSlice 0 n v | n == lengthAst v = v
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
             ( KnownNat i, KnownNat n, KnownNat k, KnownShS sh, GoodScalar r
             , AstSpan s )
          => AstShaped s r (i + n + k ': sh) -> AstShaped s r (n ': sh)
astSliceS (AstConstS t) = AstConstS $ FlipS $ tsliceS @i @n $ runFlipS t
astSliceS (Ast.AstConstantS v) = Ast.AstConstantS $ astSliceS @i @n v
astSliceS v | Just Refl <- sameNat (Proxy @i) (Proxy @0)
            , Just Refl <- sameNat (Proxy @k) (Proxy @0) = v
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
astSliceS (Ast.AstGatherS @_ @p @sh4 v ((::$) @_ @sh21 (Const var) vars, ix)) =
  let ivar = AstIntVar var + valueOf @i
      ix2 = substituteAstIndexS  -- cheap subst, because ivar is tiny
              (SubstitutionPayloadRanked @PrimalSpan @Int64 ivar)
              var ix
      vars2 = Const var ::$ vars
  in case slistKnown vars2 of
    Dict -> astGatherS @(n : sh21) @p @sh4 v (vars2, ix2)
astSliceS v = Ast.AstSliceS @i v

astReverse :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
           => AstRanked s r (1 + n) -> AstRanked s r (1 + n)
astReverse (AstConst t) = AstConst $ treverseR t
astReverse (Ast.AstConstant v) = Ast.AstConstant $ astReverse v
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

astReverseS :: forall n sh s r. (KnownNat n, KnownShS sh, GoodScalar r)
            => AstShaped s r (n ': sh) -> AstShaped s r (n ': sh)
astReverseS (AstConstS t) = AstConstS $ FlipS $ treverseS $ runFlipS t
astReverseS (Ast.AstConstantS v) = Ast.AstConstantS $ astReverseS v
astReverseS (Ast.AstFromVectorS l) = Ast.AstFromVectorS $ V.reverse l
astReverseS (Ast.AstReplicateS v) = Ast.AstReplicateS v
astReverseS (Ast.AstReverseS v) = v
astReverseS (Ast.AstGatherS v ((::$) @k (Const var) vars, ix)) =
  let ivar = valueOf @k - AstIntVar var
      ix2 = substituteAstIndexS  -- cheap subst, because ivar is tiny
              (SubstitutionPayloadRanked @PrimalSpan @Int64 ivar)
              var ix
  in astGatherS v (Const var ::$ vars, ix2)
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
  AstN2 opCode u v | not (isVar u && isVar v) ->
    AstN2 opCode (astTranspose perm u) (astTranspose perm v)
  Ast.AstR1 opCode u | not (isVar u) -> Ast.AstR1 opCode (astTranspose perm u)
  Ast.AstR2 opCode u v | not (isVar u && isVar v) ->
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
        perm3 = normalizePermutation $ backpermutePrefixList perm perm2Matched
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
  u -> Ast.AstTranspose perm u
    -- we don't go inside AstSumOfList, because they are usually long

astTransposeS :: forall perm sh s r.
                 ( PermC perm, KnownShS perm, KnownShS sh
                 , KnownNat (Sh.Rank sh), Sh.Rank perm <= Sh.Rank sh
                 , GoodScalar r, AstSpan s )
              => AstShaped s r sh -> AstShaped s r (Sh.Permute perm sh)
astTransposeS = \case
  t | Just Refl <- sameShape @perm @'[] -> t
  Ast.AstLetS var u v ->
    withShapeP (backpermutePrefixList (shapeT @perm)
                                         (shapeT @sh)) $ \(Proxy @shp) ->
      gcastWith (unsafeCoerce Refl :: Sh.Permute perm sh :~: shp) $
      astLetS var u (astTransposeS @perm v)
  AstN1S opCode u | not (isVarS u) -> AstN1S opCode (astTransposeS @perm u)
  AstN2S opCode u v | not (isVarS u && isVarS v) ->
    AstN2S opCode (astTransposeS @perm u) (astTransposeS @perm v)
  Ast.AstR1S opCode u | not (isVarS u) ->
    Ast.AstR1S opCode (astTransposeS @perm u)
  Ast.AstR2S opCode u v | not (isVarS u && isVarS v) ->
    Ast.AstR2S opCode (astTransposeS @perm u) (astTransposeS @perm v)
  Ast.AstSumS @n @sh1 v ->
    let zsuccPerm = 0 : map succ (shapeT @perm)
    in withShapeP zsuccPerm $ \(Proxy @zsuccP) ->
      gcastWith (unsafeCoerce Refl :: 0 ': MapSucc perm :~: zsuccP) $
      withShapeP (backpermutePrefixList (shapeT @perm)
                                           (shapeT @sh)) $ \(Proxy @shp) ->
        gcastWith (unsafeCoerce Refl :: Sh.Permute perm sh :~: shp) $
        gcastWith (unsafeCoerce Refl :: Sh.Rank zsuccP :~: 1 + Sh.Rank perm) $
        gcastWith (unsafeCoerce Refl
                   :: Sh.Permute zsuccP (n : sh) :~: n : Sh.Permute perm sh) $
        trustMeThisIsAPermutation @zsuccP $
        astSumS $ astTransposeS @zsuccP v
  Ast.AstScatterS @sh2 @p v (vars, ix)
    -- TODO: should the below be backpermute or permute?
    | length (shapeT @perm) <= length (shapeT @(Sh.Take p sh)) ->
      withShapeP
        (backpermutePrefixList (shapeT @perm)
                               (shapeT @sh)) $ \(Proxy @shPerm) ->
          gcastWith (unsafeCoerce Refl :: Sh.Permute perm sh :~: shPerm) $
        withShapeP (take (length ix)
                       $ shapeT @shPerm) $ \(Proxy @shpPerm) ->
          gcastWith (unsafeCoerce Refl :: Sh.Take p shPerm :~: shpPerm) $
          gcastWith (unsafeCoerce Refl
                     :: Sh.Permute perm (Sh.Take p sh) :~: shpPerm) $
          let ix2 :: AstIndexS (Sh.Take p shPerm) =
                ShapedList.backpermutePrefixIndexT @perm ix
          in gcastWith (unsafeCoerce Refl
                        :: Sh.Drop p shPerm :~: Sh.Drop p sh) $
             astScatterS @sh2 @p @shPerm v (vars, ix2)
  Ast.AstTransposeS @perm2 @sh2 t ->  -- TODO: try to perform at type level
    let permV = shapeT @perm
        perm2V = shapeT @perm2
        perm2Matched =
          perm2V
          ++ take (length permV - length perm2V) (drop (length perm2V) [0 ..])
        perm3V = normalizePermutation $ backpermutePrefixList permV perm2Matched
    in withShapeP perm3V $ \(Proxy @perm3) ->
      trustMeThisIsAPermutation @perm3 $
      gcastWith (unsafeCoerce Refl
                 :: Compare (OS.Rank perm3) (OS.Rank sh2) :~: LT) $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Permute perm3 sh2 :~: Sh.Permute perm sh) $
      astTransposeS @perm3 t
  Ast.AstGatherS @sh2 @p @sh3 v (vars, ix)
    -- TODO: should the below be backpermute or permute?
    | length (shapeT @perm) <= length (shapeT @sh2) ->
      withShapeP (backpermutePrefixList
                       (shapeT @perm)
                       (shapeT @sh2)) $ \(Proxy @shmPerm) ->
        gcastWith (unsafeCoerce Refl
                   :: Sh.Permute perm sh2 :~: shmPerm) $
        let vars2 :: AstVarListS shmPerm =
              ShapedList.backpermutePrefixSizedT @perm vars
        in gcastWith (unsafeCoerce Refl
                      :: Sh.Permute perm sh2 X.++ Sh.Drop p sh3
                         :~: Sh.Permute perm sh) $
           astGatherS @shmPerm @p @sh3 v (vars2, ix)
  -- TODO: AstConstS t -> AstConstS $ FlipS $ ttransposeS @perm $ runFlipS t
  Ast.AstConstantS v -> Ast.AstConstantS $ astTransposeS @perm v
  u -> Ast.AstTransposeS @perm u  -- TODO

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astReshapeAsGather needs to be called in addition
-- if full simplification is required.
astReshape :: forall p m s r. (KnownNat p, KnownNat m, GoodScalar r, AstSpan s)
           => ShapeInt m -> AstRanked s r p -> AstRanked s r m
astReshape shOut = \case
  Ast.AstLet var u v -> astLet var u (astReshape shOut v)
  AstN1 opCode u | not (isVar u) -> AstN1 opCode (astReshape shOut u)
  AstN2 opCode u v | not (isVar u && isVar v) ->
    AstN2 opCode (astReshape shOut u) (astReshape shOut v)
  Ast.AstR1 opCode u | not (isVar u) -> Ast.AstR1 opCode (astReshape shOut u)
  Ast.AstR2 opCode u v | not (isVar u && isVar v) ->
    Ast.AstR2 opCode (astReshape shOut u) (astReshape shOut v)
  Ast.AstFromVector l | [x] <- V.toList l -> astReshape shOut x
  Ast.AstReplicate 1 x -> astReshape shOut x
  Ast.AstReshape _ v -> astReshape shOut v
  AstConst t -> AstConst $ OR.reshape (shapeToList shOut) t
  Ast.AstConstant v -> Ast.AstConstant $ astReshape shOut v
  v -> let shIn = shapeAst v
       in case sameNat (Proxy @p) (Proxy @m) of
         Just Refl -> if shIn == shOut
                      then v
                      else Ast.AstReshape shOut v
         _ -> Ast.AstReshape shOut v

astReshapeS :: forall sh sh2 r s.
               ( KnownShS sh, KnownShS sh2, Sh.Size sh ~ Sh.Size sh2
               , GoodScalar r, AstSpan s )
            => AstShaped s r sh -> AstShaped s r sh2
astReshapeS = \case
  Ast.AstLetS var u v -> astLetS var u (astReshapeS @_ @sh2 v)
  AstN1S opCode u | not (isVarS u) -> AstN1S opCode (astReshapeS @_ @sh2 u)
  AstN2S opCode u v | not (isVarS u && isVarS v) ->
    AstN2S opCode (astReshapeS @_ @sh2 u) (astReshapeS @_ @sh2 v)
  Ast.AstR1S opCode u | not (isVarS u) ->
    Ast.AstR1S opCode (astReshapeS @_ @sh2 u)
  Ast.AstR2S opCode u v | not (isVarS u && isVarS v) ->
    Ast.AstR2S opCode (astReshapeS @_ @sh2 u) (astReshapeS @_ @sh2 v)
  Ast.AstFromVectorS @n l | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
    astReshapeS $ l V.! 0
  Ast.AstReplicateS @n x | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
    astReshapeS x
  Ast.AstReshapeS v -> astReshapeS @_ @sh2 v
  AstConstS t -> AstConstS $ FlipS $ treshapeS $ runFlipS t
  Ast.AstConstantS v -> Ast.AstConstantS $ astReshapeS v
  v -> case sameShape @sh @sh2 of
         Just Refl -> v
         _ -> Ast.AstReshapeS v

astCast :: (KnownNat n, GoodScalar r1, GoodScalar r2, RealFrac r1, RealFrac r2)
        => AstRanked s r1 n -> AstRanked s r2 n
astCast (AstConst t) = AstConst $ tcastR t
astCast (Ast.AstConstant v) = Ast.AstConstant $ astCast v
astCast (Ast.AstCast v) = astCast v
astCast (Ast.AstFromIntegral v) = astFromIntegral v
astCast v = Ast.AstCast v

astCastS :: ( KnownShS sh, GoodScalar r1, GoodScalar r2, RealFrac r1
            , RealFrac r2 )
         => AstShaped s r1 sh -> AstShaped s r2 sh
astCastS (AstConstS t) = AstConstS $ FlipS $ tcastS $ runFlipS t
astCastS (Ast.AstConstantS v) = Ast.AstConstantS $ astCastS v
astCastS (Ast.AstCastS v) = astCastS v
astCastS (Ast.AstFromIntegralS v) = astFromIntegralS v
astCastS v = Ast.AstCastS v

astFromIntegral :: (KnownNat n, GoodScalar r1, GoodScalar r2, Integral r1)
                => AstRanked PrimalSpan r1 n -> AstRanked PrimalSpan r2 n
astFromIntegral (AstConst t) = AstConst $ tfromIntegralR t
astFromIntegral (Ast.AstFromIntegral v) = astFromIntegral v
astFromIntegral v = Ast.AstFromIntegral v

astFromIntegralS :: (KnownShS sh, GoodScalar r1, GoodScalar r2, Integral r1)
                 => AstShaped PrimalSpan r1 sh -> AstShaped PrimalSpan r2 sh
astFromIntegralS (AstConstS t) = AstConstS $ FlipS $ tfromIntegralS $ runFlipS t
astFromIntegralS (Ast.AstFromIntegralS v) = astFromIntegralS v
astFromIntegralS v = Ast.AstFromIntegralS v

astProject
  :: forall n r s. (KnownNat n, GoodScalar r, AstSpan s)
  => AstHVector s -> Int -> AstRanked s r n
astProject l p = case l of
  Ast.AstMkHVector l3 -> fromDynamicR (\sh -> astReplicate0N sh 0) (l3 V.! p)
  Ast.AstLetHVectorInHVector vars d1 d2 ->
    astLetHVectorIn vars d1 (astProject d2 p)
  Ast.AstLetInHVector var u2 d2 ->
    astLet var u2 (astProject d2 p)
  Ast.AstLetInHVectorS var u2 d2 ->
    case shapeAstHVector d2 V.! p of
      DynamicRankedDummy @_ @sh _ _ | Just Refl <- matchingRank @sh @n ->
        astRFromS @sh $ astLetS var u2 $ astSFromR @sh (astProject d2 p)
      _ -> error "astProject: wrong shape"
  _ -> Ast.AstProject l p

astProjectS
  :: forall sh r s. (KnownShS sh, GoodScalar r, AstSpan s)
  => AstHVector s -> Int -> AstShaped s r sh
astProjectS l p = case l of
  Ast.AstMkHVector l3 -> fromDynamicS 0 {-(astReplicate0NS 0)-} (l3 V.! p)
  Ast.AstLetHVectorInHVector vars d1 d2 ->
    astLetHVectorInS vars d1 (astProjectS d2 p)
  Ast.AstLetInHVector var u2 d2 ->
    withListSh (Proxy @sh) $ \_ ->
      astSFromR $ astLet var u2 $ astRFromS @sh (astProjectS d2 p)
  Ast.AstLetInHVectorS var u2 d2 ->
    astLetS var u2 (astProjectS d2 p)
  _ -> Ast.AstProjectS l p

astRFromS :: forall sh s r. KnownShS sh
          => AstShaped s r sh -> AstRanked s r (Sh.Rank sh)
astRFromS (AstConstS t) | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  AstConst $ Data.Array.Convert.convert $ runFlipS t
astRFromS (Ast.AstConstantS v) = Ast.AstConstant $ astRFromS v
astRFromS (Ast.AstSFromR v) = v  -- no information lost, so no checks
astRFromS v = Ast.AstRFromS v

astSFromR :: forall sh s r. (KnownShS sh, KnownNat (Sh.Rank sh))
          => AstRanked s r (Sh.Rank sh) -> AstShaped s r sh
astSFromR (AstConst t) | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  AstConstS $ FlipS $ Data.Array.Convert.convert t
astSFromR (Ast.AstConstant v) = Ast.AstConstantS $ astSFromR v
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
  Ast.AstShare{} -> error "astPrimalPart: AstShare"
  AstN1 opCode u -> AstN1 opCode (astPrimalPart u)
  AstN2 opCode u v -> AstN2 opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstR1 opCode u -> Ast.AstR1 opCode (astPrimalPart u)
  Ast.AstR2 opCode u v -> Ast.AstR2 opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2 opCode u v -> Ast.AstI2 opCode (astPrimalPart u) (astPrimalPart v)
  AstSumOfList args -> astSumOfList (map astPrimalPart args)
  Ast.AstIndex v ix -> astIndexR (astPrimalPart v) ix
  Ast.AstSum v -> astSum (astPrimalPart v)
  Ast.AstScatter sh v (var, ix) -> astScatter sh (astPrimalPart v) (var, ix)
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
  Ast.AstProject{} -> Ast.AstPrimalPart t  -- should get simplified early
  Ast.AstLetHVectorIn vars l v -> astLetHVectorIn vars l (astPrimalPart v)
  Ast.AstLetHFunIn var f v -> astLetHFunIn var f (astPrimalPart v)
  Ast.AstRFromS v -> astRFromS $ astPrimalPartS v
  Ast.AstConstant v -> v
  Ast.AstD u _ -> u
  Ast.AstCond b a2 a3 -> astCond b (astPrimalPart a2) (astPrimalPart a3)

astPrimalPartS :: (GoodScalar r, KnownShS sh)
               => AstShaped FullSpan r sh -> AstShaped PrimalSpan r sh
astPrimalPartS t = case t of
  Ast.AstVarS{} -> Ast.AstPrimalPartS t  -- the only normal form
  Ast.AstLetS var u v -> astLetS var u (astPrimalPartS v)
  Ast.AstShareS{} -> error "astPrimalPartS: AstShareS"
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
  Ast.AstProjectS{} -> Ast.AstPrimalPartS t
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
  Ast.AstShare{} -> error "astDualPart: AstShare"
  AstN1{} -> Ast.AstDualPart t  -- stuck; the ops are not defined on dual part
  AstN2{} -> Ast.AstDualPart t  -- stuck; the ops are not defined on dual part
  Ast.AstR1{} -> Ast.AstDualPart t
  Ast.AstR2{} -> Ast.AstDualPart t
  Ast.AstI2{} -> Ast.AstDualPart t
  AstSumOfList args -> astSumOfList (map astDualPart args)
  Ast.AstIndex v ix -> astIndexR (astDualPart v) ix
  Ast.AstSum v -> astSum (astDualPart v)
  Ast.AstScatter sh v (var, ix) -> astScatter sh (astDualPart v) (var, ix)
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
  Ast.AstProject{} -> Ast.AstDualPart t
  Ast.AstLetHVectorIn vars l v -> astLetHVectorIn vars l (astDualPart v)
  Ast.AstLetHFunIn var f v -> astLetHFunIn var f (astDualPart v)
  Ast.AstRFromS v -> astRFromS $ astDualPartS v
  Ast.AstConstant{}  -> Ast.AstDualPart t  -- this equals nil (not primal 0)
  Ast.AstD _ u' -> u'
  Ast.AstCond b a2 a3 -> astCond b (astDualPart a2) (astDualPart a3)

astDualPartS :: (GoodScalar r, KnownShS sh)
             => AstShaped FullSpan r sh -> AstShaped DualSpan r sh
astDualPartS t = case t of
  Ast.AstVarS{} -> Ast.AstDualPartS t
  Ast.AstLetS var u v -> astLetS var u (astDualPartS v)
  Ast.AstShareS{} -> error "astDualPartS: AstShareS"
  AstN1S{} -> Ast.AstDualPartS t
  AstN2S{} -> Ast.AstDualPartS t
  Ast.AstR1S{} -> Ast.AstDualPartS t
  Ast.AstR2S{} -> Ast.AstDualPartS t
  Ast.AstI2S{} -> Ast.AstDualPartS t
  AstSumOfListS args -> astSumOfListS (map astDualPartS args)
  Ast.AstIndexS v ix -> Ast.AstIndexS (astDualPartS v) ix
  Ast.AstSumS v -> astSumS (astDualPartS v)
  Ast.AstScatterS v (var, ix) -> astScatterS (astDualPartS v) (var, ix)
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
  Ast.AstProjectS{} -> Ast.AstDualPartS t
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
  -> (forall sh r. (KnownShS sh, GoodScalar r)
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
          fRanked (AstVarName varId) (astRFromS @sh3 @_ @r3 ({-srepl-} 0)) acc
  DynamicShapedDummy @r4 @sh4 _ _
    | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
    , Just Refl <- sameShape @sh3 @sh4
    , Just Refl <- testEquality (typeRep @r3) (typeRep @r4) ->
        fShaped @sh4 @r4 (AstVarName varId) ({-srepl-} 0) acc
  _ -> error $ "mapRankedShaped: corrupted arguments"
               `showFailure`
               ( vd, typeRep @ty, typeRep @r3, shapeT @sh3
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
                    (GoodScalar r, KnownShS sh, AstSpan s, AstSpan s2)
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
  in withShapeP (shapeToList sh) $ \proxy -> case proxy of
    Proxy @sh | Just Refl <- matchingRank @sh @n -> case l of
      Ast.AstMkHVector l3 ->
        let f :: forall sh1 r1. (KnownShS sh1, GoodScalar r1)
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
      Ast.AstLetInHVectorS var2 u2 d2 ->
        astRFromS $ astLetS var2 u2 $ astSFromR @sh
        $ astLetHVectorIn vars d2 v
      _ -> Ast.AstLetHVectorIn vars l v
    _ -> error "astLetHVectorIn: wrong rank of the argument"

-- Inlining doesn't work for this let constructor, because it has many
-- variables, so we try to reduce it to another for which it works.
astLetHVectorInS
  :: forall sh r s s2. (KnownShS sh, GoodScalar r, AstSpan s, AstSpan s2)
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
    Ast.AstLetInHVectorS var2 u2 d2 ->
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

simplifyAstInt :: AstInt -> AstInt
simplifyAstInt = simplifyAst

simplifyAstIndex :: AstIndex n -> AstIndex n
simplifyAstIndex = fmap simplifyAstInt

simplifyAstIndexS :: AstIndexS sh -> AstIndexS sh
simplifyAstIndexS = fmap simplifyAstInt

-- | This function guarantees full simplification: every redex
-- is visited and each combinator applied. The most exhaustive and costly
-- variants of each combinator are used, e.g., astIndexR.
simplifyAst
  :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
  => AstRanked s r n -> AstRanked s r n
simplifyAst t = case t of
  Ast.AstVar{} -> t
  Ast.AstLet var u v -> astLet var (simplifyAst u) (simplifyAst v)
  Ast.AstShare{} -> error "simplifyAst: AstShare"
  Ast.AstCond b a2 a3 ->
    astCond (simplifyAstBool b) (simplifyAst a2) (simplifyAst a3)
  Ast.AstMinIndex a -> Ast.AstMinIndex (simplifyAst a)
  Ast.AstMaxIndex a -> Ast.AstMaxIndex (simplifyAst a)
  Ast.AstFloor a -> Ast.AstFloor (simplifyAst a)
  Ast.AstIota -> t
  AstN1 opCode u ->
    case isRankedInt u of
      Just Refl -> contractAstNumOp1 opCode (simplifyAst u)
      _ -> AstN1 opCode (simplifyAst u)
  AstN2 opCode u v ->
    case isRankedInt u of
      Just Refl -> contractAstNumOp2 opCode (simplifyAst u) (simplifyAst v)
      _ -> AstN2 opCode (simplifyAst u) (simplifyAst v)
  Ast.AstR1 opCode u -> Ast.AstR1 opCode (simplifyAst u)
  Ast.AstR2 opCode u v -> Ast.AstR2 opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2 opCode u v ->
    case isRankedInt u of
      Just Refl -> contractAstIntegralOp2 opCode (simplifyAst u) (simplifyAst v)
      _ -> Ast.AstI2 opCode (simplifyAst u) (simplifyAst v)
  AstSumOfList args ->
    case isRankedInt t of
      Just Refl -> foldr1 contractAstPlusOp (map simplifyAst args)
      _ -> astSumOfList (map simplifyAst args)
  Ast.AstIndex v ix -> astIndexR (simplifyAst v) (simplifyAstIndex ix)
  Ast.AstSum v -> astSum (simplifyAst v)
  Ast.AstScatter sh v (var, ix) ->
    astScatter sh (simplifyAst v) (var, simplifyAstIndex ix)
  Ast.AstFromVector l -> astFromVector (V.map simplifyAst l)
  Ast.AstReplicate k v -> astReplicate k (simplifyAst v)
  Ast.AstAppend x y -> astAppend (simplifyAst x) (simplifyAst y)
  Ast.AstSlice i k v -> astSlice i k (simplifyAst v)
  Ast.AstReverse v -> astReverse (simplifyAst v)
  Ast.AstTranspose perm v ->
    astTranspose (normalizePermutation perm) (simplifyAst v)
  Ast.AstReshape sh v -> astReshape sh (simplifyAst v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, simplifyAst v)
  Ast.AstGather sh v (vars, ix) ->
    astGatherR sh (simplifyAst v) (vars, simplifyAstIndex ix)
  Ast.AstCast v -> astCast $ simplifyAst v
  Ast.AstFromIntegral v -> astFromIntegral $ simplifyAst v
  AstConst{} -> t
  Ast.AstProject l p -> astProject (simplifyAstHVector l) p
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
  :: (KnownShS sh, GoodScalar r, AstSpan s)
  => AstShaped s r sh -> AstShaped s r sh
simplifyAstS t = case t of
  Ast.AstVarS{} -> t
  Ast.AstLetS var u v -> astLetS var (simplifyAstS u) (simplifyAstS v)
  Ast.AstShareS{} -> error "simplifyAstS: AstShareS"
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
  Ast.AstIndexS v ix -> astIndexS (simplifyAstS v) (simplifyAstIndexS ix)
  Ast.AstSumS v -> astSumS (simplifyAstS v)
  Ast.AstScatterS v (var, ix) ->
    astScatterS (simplifyAstS v) (var, simplifyAstIndexS ix)
  Ast.AstFromVectorS l -> astFromVectorS (V.map simplifyAstS l)
  Ast.AstReplicateS v -> astReplicateS (simplifyAstS v)
  Ast.AstAppendS x y -> astAppendS (simplifyAstS x) (simplifyAstS y)
  Ast.AstSliceS @i v -> astSliceS @i (simplifyAstS v)
  Ast.AstReverseS v -> astReverseS (simplifyAstS v)
  Ast.AstTransposeS @perm v -> astTransposeS @perm $ simplifyAstS v
  Ast.AstReshapeS v -> astReshapeS $ simplifyAstS v
  Ast.AstBuild1S (var, v) -> Ast.AstBuild1S (var, simplifyAstS v)
  Ast.AstGatherS v (vars, ix) ->
    astGatherS (simplifyAstS v) (vars, simplifyAstIndexS ix)
  Ast.AstCastS v -> astCastS $ simplifyAstS v
  Ast.AstFromIntegralS v -> astFromIntegralS $ simplifyAstS v
  AstConstS{} -> t
  Ast.AstProjectS l p -> astProjectS (simplifyAstHVector l) p
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
  Ast.AstShareHVector{} -> error "simplifyAstHVector: AstShareHVector"
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
    contractAstB2 opCodeBool (simplifyAstBool arg1) (simplifyAstBool arg2)
  AstBoolConst{} -> t
  Ast.AstRel opCodeRel arg1 arg2 ->
    contractRelOp opCodeRel (simplifyAst arg1) (simplifyAst arg2)
      -- These expressions potentially represent large tensors that are
      -- expensive to compute even when constant so we simplify and ignore them,
      -- because computation should be done on GPU, not on CPU when simplifying;
      -- we'd need a flag to control how much we pre-compute.
      -- Anyway, because these tensors sometimes represent indexes,
      -- we simplify them a bit more than the shaped ones.
  Ast.AstRelS opCodeRel arg1 arg2 ->
    Ast.AstRelS opCodeRel (simplifyAstS arg1) (simplifyAstS arg2)


-- * The expanding (to gather expressions) bottom-up pass

expandAstInt :: AstInt -> AstInt
expandAstInt = expandAst

expandAstIndex :: AstIndex n -> AstIndex n
expandAstIndex = fmap expandAstInt

expandAstIndexS :: AstIndexS sh -> AstIndexS sh
expandAstIndexS = fmap expandAstInt

expandAst
  :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
  => AstRanked s r n -> AstRanked s r n
expandAst t = case t of
  Ast.AstVar{} -> t
  Ast.AstLet var u v -> astLet var (expandAst u) (expandAst v)
  Ast.AstShare{} -> error "expandAst: AstShare"
  Ast.AstCond b a2 a3 ->
    astCond (expandAstBool b) (expandAst a2) (expandAst a3)
  Ast.AstMinIndex a -> Ast.AstMinIndex (expandAst a)
  Ast.AstMaxIndex a -> Ast.AstMaxIndex (expandAst a)
  Ast.AstFloor a -> Ast.AstFloor (expandAst a)
  Ast.AstIota -> t
  AstN1 opCode u ->
    case isRankedInt u of
      Just Refl -> contractAstNumOp1 opCode (expandAst u)
      _ -> AstN1 opCode (expandAst u)
  AstN2 opCode u v ->
    case isRankedInt u of
      Just Refl -> contractAstNumOp2 opCode (expandAst u) (expandAst v)
      _ -> case opCode of
        TimesOp | Just Refl <- sameNat (Proxy @n) (Proxy @3) ->
          AstN2 opCode (simplifyAst u) (simplifyAst v)
            -- TODO: a workaround for interpretMatmul2 not yet generalized
            -- to gathers (and moved from AstInterpret here, ideally)
        _ -> AstN2 opCode (expandAst u) (expandAst v)
  Ast.AstR1 opCode u -> Ast.AstR1 opCode (expandAst u)
  Ast.AstR2 opCode u v -> Ast.AstR2 opCode (expandAst u) (expandAst v)
  Ast.AstI2 opCode u v ->
    case isRankedInt u of
      Just Refl -> contractAstIntegralOp2 opCode (expandAst u) (expandAst v)
      _ -> Ast.AstI2 opCode (expandAst u) (expandAst v)
  AstSumOfList args ->
    case isRankedInt t of
      Just Refl -> foldr1 contractAstPlusOp (map expandAst args)
      _ -> astSumOfList (map expandAst args)
  Ast.AstIndex v ix -> astIndexKnobsR (defaultKnobs {knobExpand = True})
                                      (expandAst v)
                                      (expandAstIndex ix)
  Ast.AstSum v -> astSum (expandAst v)
  Ast.AstScatter sh v (var, ix) ->
    astScatter sh (expandAst v) (var, expandAstIndex ix)
  Ast.AstFromVector l -> astFromVector (V.map expandAst l)
  Ast.AstReplicate k v -> astReplicate k (expandAst v)
  Ast.AstAppend x y -> astAppend (expandAst x) (expandAst y)
  Ast.AstSlice i k v -> astSlice i k (expandAst v)
  Ast.AstReverse v -> astReverse (expandAst v)
  Ast.AstTranspose perm v -> case v of
    Ast.AstVar{} -> t  -- normal form
    AstN1 _ w | isVar w -> t  -- normal form
    AstN2 _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstR1 _ w | isVar w -> t  -- normal form
    Ast.AstR2 _ x y | isVar x && isVar y -> t  -- normal form
    AstSumOfList{} -> t  -- normal form
    Ast.AstScatter @_ @_ @p _ _ _ | length perm > valueOf @p -> t  -- nf
    Ast.AstReplicate{} -> t  -- normal form
      -- TODO: this nf is silly, but right now transposes of replicates
      -- are small OR.Arrays and equivalent gathers are large OR.Arrays,
      -- so this has to stay. Maybe we should contract gathers back
      -- to transposes of replicates (not only to replicates). Or maybe
      -- we should extend orthotope to any gather schemes, not only
      -- the simple ones.
    _ ->  -- not nf, let's express all as a gather
      astTransposeAsGather (defaultKnobs {knobExpand = True})
                           (normalizePermutation perm)
                           (expandAst v)
        -- this is expensive but the only way to guarantee full simplification
  Ast.AstReshape sh v -> case v of
    Ast.AstVar{} -> t  -- normal form
    AstN1 _ w | isVar w -> t  -- normal form
    AstN2 _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstR1 _ w | isVar w -> t  -- normal form
    Ast.AstR2 _ x y | isVar x && isVar y -> t  -- normal form
    AstSumOfList{} -> t  -- normal form
    Ast.AstScatter{} -> t  -- normal form
    _ ->  -- not nf, let's express all as a gather
      astReshapeAsGather (defaultKnobs {knobExpand = True})
                         sh
                         (expandAst v)
        -- this is expensive but the only way to guarantee full simplification
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, expandAst v)
  Ast.AstGather sh v (vars, ix) ->
    astGatherKnobsR (defaultKnobs {knobExpand = True})
                    sh (expandAst v) (vars, expandAstIndex ix)
  Ast.AstCast v -> astCast $ expandAst v
  Ast.AstFromIntegral v -> astFromIntegral $ expandAst v
  AstConst{} -> t
  Ast.AstProject l p -> astProject (expandAstHVector l) p
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars (expandAstHVector l) (expandAst v)
  Ast.AstLetHFunIn var f v ->
    astLetHFunIn var (expandAstHFun f) (expandAst v)
  Ast.AstRFromS v -> astRFromS $ expandAstS v
  Ast.AstConstant v -> Ast.AstConstant (expandAst v)
  Ast.AstPrimalPart v -> astPrimalPart (expandAst v)
  Ast.AstDualPart v -> astDualPart (expandAst v)
  Ast.AstD u u' -> Ast.AstD (expandAst u) (expandAst u')

expandAstS
  :: (KnownShS sh, GoodScalar r, AstSpan s)
  => AstShaped s r sh -> AstShaped s r sh
expandAstS t = case t of
  Ast.AstVarS{} -> t
  Ast.AstLetS var u v -> astLetS var (expandAstS u) (expandAstS v)
  Ast.AstShareS{} -> error "expandAstS: AstShareS"
  Ast.AstCondS b a2 a3 ->
    astCondS (expandAstBool b) (expandAstS a2) (expandAstS a3)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (expandAstS a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (expandAstS a)
  Ast.AstFloorS a -> Ast.AstFloorS (expandAstS a)
  Ast.AstIotaS -> t
  AstN1S opCode u -> AstN1S opCode (expandAstS u)
  AstN2S opCode u v -> AstN2S opCode (expandAstS u) (expandAstS v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (expandAstS u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (expandAstS u) (expandAstS v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (expandAstS u) (expandAstS v)
  AstSumOfListS args -> astSumOfListS (map expandAstS args)
  Ast.AstIndexS v ix -> astIndexKnobsS (defaultKnobs {knobExpand = True})
                                       (expandAstS v)
                                       (expandAstIndexS ix)
  Ast.AstSumS v -> astSumS (expandAstS v)
  Ast.AstScatterS v (var, ix) ->
    astScatterS (expandAstS v) (var, expandAstIndexS ix)
  Ast.AstFromVectorS l -> astFromVectorS (V.map expandAstS l)
  Ast.AstReplicateS v -> astReplicateS (expandAstS v)
  Ast.AstAppendS x y -> astAppendS (expandAstS x) (expandAstS y)
  Ast.AstSliceS @i v -> astSliceS @i (expandAstS v)
  Ast.AstReverseS v -> astReverseS (expandAstS v)
  Ast.AstTransposeS @perm v -> astTransposeS @perm $ expandAstS v
  Ast.AstReshapeS v -> astReshapeS $ expandAstS v
  Ast.AstBuild1S (var, v) -> Ast.AstBuild1S (var, expandAstS v)
  Ast.AstGatherS v (vars, ix) ->
    astGatherKnobsS (defaultKnobs {knobExpand = True})
                    (expandAstS v) (vars, expandAstIndexS ix)
  Ast.AstCastS v -> astCastS $ expandAstS v
  Ast.AstFromIntegralS v -> astFromIntegralS $ expandAstS v
  AstConstS{} -> t
  Ast.AstProjectS l p -> astProjectS (expandAstHVector l) p
  Ast.AstLetHVectorInS vars l v ->
    astLetHVectorInS vars (expandAstHVector l) (expandAstS v)
  Ast.AstLetHFunInS var f v ->
    astLetHFunInS var (expandAstHFun f) (expandAstS v)
  Ast.AstSFromR v -> astSFromR $ expandAst v
  Ast.AstConstantS v -> Ast.AstConstantS (expandAstS v)
  Ast.AstPrimalPartS v -> astPrimalPartS (expandAstS v)
  Ast.AstDualPartS v -> astDualPartS (expandAstS v)
  Ast.AstDS u u' -> Ast.AstDS (expandAstS u) (expandAstS u')

expandAstDynamic
  :: AstSpan s
  => AstDynamic s -> AstDynamic s
expandAstDynamic (DynamicRanked u) =
  DynamicRanked $ expandAst u
expandAstDynamic (DynamicShaped u) =
  DynamicShaped $ expandAstS u
expandAstDynamic u@DynamicRankedDummy{} = u
expandAstDynamic u@DynamicShapedDummy{} = u

expandAstHVector
  :: AstSpan s => AstHVector s -> AstHVector s
expandAstHVector = \case
  Ast.AstMkHVector l -> Ast.AstMkHVector $ V.map expandAstDynamic l
  Ast.AstHApply t ll -> astHApply (expandAstHFun t)
                                  (map (V.map expandAstDynamic) ll)
  Ast.AstLetHVectorInHVector vars u v ->
    astLetHVectorInHVector vars (expandAstHVector u) (expandAstHVector v)
  Ast.AstLetHFunInHVector var f v ->
    astLetHFunInHVector var (expandAstHFun f) (expandAstHVector v)
  Ast.AstLetInHVector var u v ->
    astLetInHVector var (expandAst u) (expandAstHVector v)
  Ast.AstLetInHVectorS var u v ->
    astLetInHVectorS var (expandAstS u) (expandAstHVector v)
  Ast.AstShareHVector{} -> error "expandAstHVector: AstShareHVector"
  Ast.AstBuildHVector1 k (var, v) ->
    Ast.AstBuildHVector1 k (var, expandAstHVector v)
  Ast.AstMapAccumRDer k accShs bShs eShs f df rf acc0 es ->
    Ast.AstMapAccumRDer k accShs bShs eShs
                        (expandAstHFun f)
                        (expandAstHFun df)
                        (expandAstHFun rf)
                        (expandAstHVector acc0)
                        (expandAstHVector es)
  Ast.AstMapAccumLDer k accShs bShs eShs f df rf acc0 es ->
    Ast.AstMapAccumLDer k accShs bShs eShs
                        (expandAstHFun f)
                        (expandAstHFun df)
                        (expandAstHFun rf)
                        (expandAstHVector acc0)
                        (expandAstHVector es)

expandAstHFun :: AstHFun -> AstHFun
expandAstHFun = \case
  Ast.AstLambda ~(vvars, l) -> Ast.AstLambda (vvars, expandAstHVector l)
  t@(Ast.AstVarHFun{}) -> t

expandAstBool :: AstBool -> AstBool
expandAstBool t = case t of
  Ast.AstBoolNot (AstBoolConst b) -> AstBoolConst $ not b
  Ast.AstBoolNot arg -> Ast.AstBoolNot $ expandAstBool arg
  Ast.AstB2 opCodeBool arg1 arg2 ->
    contractAstB2 opCodeBool (expandAstBool arg1) (expandAstBool arg2)
  AstBoolConst{} -> t
  Ast.AstRel opCodeRel arg1 arg2 ->
    contractRelOp opCodeRel (expandAst arg1) (expandAst arg2)
      -- These expressions potentially represent large tensors that are
      -- expensive to compute even when constant so we expand and ignore them,
      -- because computation should be done on GPU, not on CPU when expanding;
      -- we'd need a flag to control how much we pre-compute.
      -- Anyway, because these tensors sometimes represent indexes,
      -- we expand them a bit more than the shaped ones.
  Ast.AstRelS opCodeRel arg1 arg2 ->
    Ast.AstRelS opCodeRel (expandAstS arg1) (expandAstS arg2)


-- * Contraction of arithmetic and boolean operation terms

-- TODO: when we have more tests, try to limit this rewrite
-- (or only the first half) to Int64 at rank 0 and see if performance improves
-- even more.
contractRelOp :: (KnownNat n, GoodScalar r)
              => OpCodeRel
              -> AstRanked PrimalSpan r n -> AstRanked PrimalSpan r n
              -> AstBool
contractRelOp EqOp (AstConst u) (AstConst v) = AstBoolConst $ u == v
contractRelOp NeqOp (AstConst u) (AstConst v) = AstBoolConst $ u /= v
contractRelOp LeqOp (AstConst u) (AstConst v) = AstBoolConst $ u <= v
contractRelOp GeqOp (AstConst u) (AstConst v) = AstBoolConst $ u >= v
contractRelOp LsOp (AstConst u) (AstConst v) = AstBoolConst $ u < v
contractRelOp GtOp (AstConst u) (AstConst v) = AstBoolConst $ u > v
contractRelOp EqOp (Ast.AstVar _ u) (Ast.AstVar _ v) | u == v =
  AstBoolConst True
contractRelOp LeqOp (Ast.AstVar _ u) (Ast.AstVar _ v) | u == v =
  AstBoolConst True
contractRelOp GeqOp (Ast.AstVar _ u) (Ast.AstVar _ v) | u == v =
  AstBoolConst True
contractRelOp NeqOp (Ast.AstVar _ u) (Ast.AstVar _ v) | u == v =
  AstBoolConst False
contractRelOp LsOp (Ast.AstVar _ u) (Ast.AstVar _ v) | u == v =
  AstBoolConst False
contractRelOp GtOp (Ast.AstVar _ u) (Ast.AstVar _ v) | u == v =
  AstBoolConst False
contractRelOp opCodeRel arg1 arg2 = Ast.AstRel opCodeRel arg1 arg2

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
contractAstPlusOp :: AstInt -> AstInt -> AstInt
contractAstPlusOp (AstSumOfList (AstConst u : lu))
                  (AstSumOfList (AstConst v : lv)) =
  addConstToList (u + v) (lu ++ lv)
contractAstPlusOp (AstSumOfList lu)
                  (AstSumOfList (AstConst v : lv)) =
  AstSumOfList (AstConst v : lv ++ lu)
contractAstPlusOp (AstSumOfList lu)
                  (AstSumOfList lv) =
  AstSumOfList (lu ++ lv)

contractAstPlusOp (AstConst u)
                  (AstSumOfList (AstConst v : lv)) =
  addConstToList (u + v) lv
contractAstPlusOp u
                  (AstSumOfList (AstConst v : lv)) =
  AstSumOfList (AstConst v : u : lv)
contractAstPlusOp u
                  (AstSumOfList lv) =
  AstSumOfList (u : lv)

contractAstPlusOp (AstSumOfList (AstConst u : lu))
                  (AstConst v) =
  addConstToList (u + v) lu
contractAstPlusOp (AstSumOfList (AstConst u : lu))
                  v =
  AstSumOfList (AstConst u : v : lu)
contractAstPlusOp (AstSumOfList lu)
                  v =
  AstSumOfList (v : lu)

contractAstPlusOp (AstConst u) (AstConst v) = AstConst $ u + v
contractAstPlusOp u (AstConst v) = addConstToList v [u]
contractAstPlusOp (AstConst u) v = addConstToList u [v]

-- Unfortunately, these won't fire if the required terms are scattered
-- among elements of the AstSumOfList list. However, in many cases,
-- binary addition is used interspersed with other operations,
-- so longer lists don't form and so these terms have a chance to be adjacent,
-- especially that AstConst is guaranteed not to intervene.
contractAstPlusOp (AstN1 NegateOp (Ast.AstVar _ var))
                  (Ast.AstVar _ var')
  | var == var' = 0
contractAstPlusOp (Ast.AstVar _ var')
                  (AstN1 NegateOp (Ast.AstVar _ var))
  | var == var' = 0
contractAstPlusOp
  (Ast.AstI2 RemOp (AstN1 NegateOp (Ast.AstVar _ var)) (AstConst v))
  (Ast.AstI2 RemOp (Ast.AstVar _ var') (AstConst v'))
  | var == var' && v == v' = 0
contractAstPlusOp
  (Ast.AstI2 RemOp (Ast.AstVar _ var') (AstConst v'))
  (Ast.AstI2 RemOp (AstN1 NegateOp (Ast.AstVar _ var)) (AstConst v))
  | var == var' && v == v' = 0

contractAstPlusOp u v = AstSumOfList [u, v]

addConstToList :: OR.Array 0 Int64 -> [AstInt] -> AstInt
addConstToList _ [] = error "addConstToList: AstSumOfList list too short"
addConstToList arr [i] =
  if OR.allA (== 0) arr then i else AstSumOfList [AstConst arr, i]
addConstToList arr l =
  if OR.allA (== 0) arr then AstSumOfList l else AstSumOfList (AstConst arr : l)

contractAstNumOp1 :: OpCodeNum1 -> AstInt -> AstInt
contractAstNumOp1 NegateOp (AstConst u) = AstConst $ negate u
contractAstNumOp1 NegateOp (AstSumOfList l) =
  foldr1 contractAstPlusOp (map (contractAstNumOp1 NegateOp) l)
contractAstNumOp1 NegateOp (AstN2 TimesOp (AstConst u) v) =
  contractAstNumOp2 TimesOp (AstConst $ negate u) v
    -- given a choice, prefer to negate a constant
contractAstNumOp1 NegateOp (AstN2 TimesOp u v) =
  contractAstNumOp2 TimesOp u (contractAstNumOp1 NegateOp v)
contractAstNumOp1 NegateOp (AstN1 NegateOp u) = u
contractAstNumOp1 NegateOp (AstN1 SignumOp u) =
  contractAstNumOp1 SignumOp (contractAstNumOp1 NegateOp u)
contractAstNumOp1 NegateOp (Ast.AstI2 QuotOp u v) =
  contractAstIntegralOp2 QuotOp (contractAstNumOp1 NegateOp u) v
    -- v is likely positive and let's keep it so
contractAstNumOp1 NegateOp (Ast.AstI2 RemOp u v) =
  contractAstIntegralOp2 RemOp (contractAstNumOp1 NegateOp u) v
    -- v is likely positive and let's keep it so

contractAstNumOp1 AbsOp (AstConst u) = AstConst $ abs u
contractAstNumOp1 AbsOp (AstN1 AbsOp u) = AstN1 AbsOp u
contractAstNumOp1 AbsOp (AstN1 NegateOp u) = contractAstNumOp1 AbsOp u
contractAstNumOp1 SignumOp (AstConst u) = AstConst $ signum u
contractAstNumOp1 SignumOp (AstN1 SignumOp u) = AstN1 SignumOp u
contractAstNumOp1 SignumOp (AstN1 AbsOp u) =
  contractAstNumOp1 AbsOp (AstN1 SignumOp u)

contractAstNumOp1 opCode u = AstN1 opCode u

contractAstNumOp2 :: OpCodeNum2 -> AstInt -> AstInt -> AstInt
contractAstNumOp2 MinusOp u v =
  contractAstPlusOp u (contractAstNumOp1 NegateOp v)
contractAstNumOp2 TimesOp (AstConst u) (AstConst v) = AstConst $ u * v
contractAstNumOp2 TimesOp (AstConst 0) _v = AstConst 0
contractAstNumOp2 TimesOp _u (AstConst 0) = AstConst 0
contractAstNumOp2 TimesOp (AstConst 1) v = v
contractAstNumOp2 TimesOp u (AstConst 1) = u
{- TODO: is it worth adding AstLet with a fresh variables
   to share w and so make these rules safe? Perhaps after we decide
   a normal form (e.g., a polynomial)?
contractAstNumOp TimesOp (AstN2 PlusOp (u, v), w) =
  contractAstPlusOp ( contractAstNumOp TimesOp (u, w)
                    , contractAstNumOp TimesOp (v, w) )
contractAstNumOp TimesOp (u, AstN2 PlusOp (v, w)) =
  contractAstPlusOp ( contractAstNumOp TimesOp (u, v)
                    , contractAstNumOp TimesOp (u, w) )
-}
contractAstNumOp2 TimesOp (AstSumOfList l) w@AstConst{} =
  foldr1 contractAstPlusOp (map (\u -> contractAstNumOp2 TimesOp u w) l)
contractAstNumOp2 TimesOp u@AstConst{} (AstSumOfList l) =
  foldr1 contractAstPlusOp (map (contractAstNumOp2 TimesOp u) l)
-- TODO: perhaps aim for a polynomial normal form? but that requires global
-- inspection of the whole expression
contractAstNumOp2 TimesOp (AstConst u) (AstN2 TimesOp (AstConst v) w) =
  contractAstNumOp2 TimesOp (AstConst $ u * v) w
contractAstNumOp2 TimesOp u (AstConst n) =
  contractAstNumOp2 TimesOp (AstConst n) u
contractAstNumOp2 TimesOp (AstN2 TimesOp u v) w =
  contractAstNumOp2 TimesOp u (contractAstNumOp2 TimesOp v w)

-- With static shapes, the second argument to QuotOp and RemOp
-- is often a constant, which makes such rules worth including,
-- since they are likely to fire. To help them fire, we avoid changing
-- that constant, if possible, e.g., in rules for NegateOp.
contractAstNumOp2
  TimesOp (AstConst v)
          (Ast.AstI2 QuotOp (Ast.AstVar sh var) (AstConst v')) | v == v' =
    contractAstNumOp2 MinusOp
                      (Ast.AstVar sh var)
                      (Ast.AstI2 RemOp (Ast.AstVar sh var) (AstConst v))
contractAstNumOp2 opCode u v = AstN2 opCode u v

contractAstIntegralOp2 :: OpCodeIntegral2 -> AstInt -> AstInt -> AstInt
contractAstIntegralOp2 QuotOp (AstConst u) (AstConst v) = AstConst $ quot u v
contractAstIntegralOp2 QuotOp (AstConst 0) _v = AstConst 0
contractAstIntegralOp2 QuotOp u (AstConst 1) = u
contractAstIntegralOp2 QuotOp (Ast.AstI2 RemOp _u (AstConst v)) (AstConst v')
  | v' >= v && v >= 0 = 0
contractAstIntegralOp2 QuotOp (Ast.AstI2 QuotOp u v) w =
  contractAstIntegralOp2 QuotOp u (contractAstNumOp2 TimesOp v w)
contractAstIntegralOp2 QuotOp (Ast.AstN2 TimesOp (AstConst u) v) (AstConst u')
  | u == u' = v

contractAstIntegralOp2 RemOp (AstConst u) (AstConst v) = AstConst $ rem u v
contractAstIntegralOp2 RemOp (AstConst 0) _v = 0
contractAstIntegralOp2 RemOp _u (AstConst 1) = 0
contractAstIntegralOp2 RemOp (Ast.AstI2 RemOp u (AstConst v)) (AstConst v')
  | v' >= v && v >= 0 = Ast.AstI2 RemOp u (AstConst v)
contractAstIntegralOp2 RemOp (Ast.AstI2 RemOp u (AstConst v)) (AstConst v')
  | rem v v' == 0 && v > 0 = contractAstIntegralOp2 RemOp u (AstConst v')
contractAstIntegralOp2 RemOp (AstN2 TimesOp (AstConst u) _v) (AstConst u')
  | rem u u' == 0 = 0

contractAstIntegralOp2 opCode u v = Ast.AstI2 opCode u v

-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right.
contractAstB2 :: OpCodeBool -> AstBool -> AstBool -> AstBool
contractAstB2 AndOp (AstBoolConst True) b = b
contractAstB2 AndOp (AstBoolConst False) _b = AstBoolConst False
contractAstB2 AndOp b (AstBoolConst True) = b
contractAstB2 AndOp _b (AstBoolConst False) = AstBoolConst False
contractAstB2 OrOp (AstBoolConst True) _b = AstBoolConst True
contractAstB2 OrOp (AstBoolConst False) b = b
contractAstB2 OrOp _b (AstBoolConst True) = AstBoolConst True
contractAstB2 OrOp b (AstBoolConst False) = b
contractAstB2 opCodeBool arg1 arg2 = Ast.AstB2 opCodeBool arg1 arg2


-- * Substitution payload and adaptors for AstVarName

-- | The term to substitute for a variable. Without this variant type,
-- we'd need to duplicate the whole sibstitution code, one copy
-- for each of the cases.
type role SubstitutionPayload nominal nominal
  -- r can't be representational due to AstRanked having it as nominal
data SubstitutionPayload :: AstSpanType -> Type -> Type where
  SubstitutionPayloadRanked :: forall s r n. KnownNat n
                            => AstRanked s r n -> SubstitutionPayload s r
  SubstitutionPayloadShaped :: forall s r sh. KnownShS sh
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
                  ( GoodScalar r, GoodScalar r2, KnownShS sh
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

substituteAstBool
  :: (GoodScalar r2, AstSpan s2)
  => SubstitutionPayload s2 r2 -> AstVarName (f s2) r2 y -> AstBool
  -> AstBool
substituteAstBool i (AstVarName varId) v1 =
  fromMaybe v1 $ substitute1AstBool i varId v1


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
        Just Refl -> case shapeToList sh == shapeT @sh2 of
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
  Ast.AstShare{} -> error "substitute1Ast: AstShare"
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
       Just Refl -> contractAstNumOp1 opCode u2
       _ -> Ast.AstN1 opCode u2)
    <$> substitute1Ast i var u
  Ast.AstN2 opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ case isRankedInt u of
         Just Refl -> contractAstNumOp2 opCode (fromMaybe u mu) (fromMaybe v mv)
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
           contractAstIntegralOp2 opCode (fromMaybe u mu) (fromMaybe v mv)
         _ -> Ast.AstI2 opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstSumOfList args ->
    let margs = map (substitute1Ast i var) args
    in if any isJust margs
       then Just $ case isRankedInt v1 of
         Just Refl -> foldr1 contractAstPlusOp $ zipWith fromMaybe args margs
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
  Ast.AstProject l p ->
    case substitute1AstHVector i var l of
      Nothing -> Nothing
      ml -> Just $ astProject (fromMaybe l ml) p
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
                   ( GoodScalar r, GoodScalar r2, KnownShS sh
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
            Just Refl -> assert (shapeT @sh == shapeToList (shapeAst t))
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
  Ast.AstShareS{} -> error "substitute1AstS: AstShareS"
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
      (mv, mix) -> Just $ astIndexS (fromMaybe v mv) (fromMaybe ix mix)
  Ast.AstSumS v -> astSumS <$> substitute1AstS i var v
  Ast.AstScatterS v (vars, ix) ->
    case (substitute1AstS i var v, substitute1AstIndexS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astScatterS (fromMaybe v mv)
                                      (vars, fromMaybe ix mix)
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
  Ast.AstProjectS l p ->
    case substitute1AstHVector i var l of
      Nothing -> Nothing
      ml -> Just $ astProjectS (fromMaybe l ml) p
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
     then Just $ ShapedList.zipWith_Index fromMaybe ix mix
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
  Ast.AstShareHVector{} -> error "substitute1AstHVector: AstShareHVector"
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
       then Just $ contractAstB2 opCodeBool (fromMaybe arg1 mb1)
                                            (fromMaybe arg2 mb2)
       else Nothing
  Ast.AstBoolConst{} -> Nothing
  Ast.AstRel opCodeRel arg1 arg2 ->
    let mr1 = substitute1Ast i var arg1
        mr2 = substitute1Ast i var arg2
    in if isJust mr1 || isJust mr2
       then Just $ contractRelOp opCodeRel (fromMaybe arg1 mr1)
                                           (fromMaybe arg2 mr2)
       else Nothing
  Ast.AstRelS opCodeRel arg1 arg2 ->
    let mr1 = substitute1AstS i var arg1
        mr2 = substitute1AstS i var arg2
    in if isJust mr1 || isJust mr2
       then Just $ Ast.AstRelS opCodeRel (fromMaybe arg1 mr1)
                                         (fromMaybe arg2 mr2)
       else Nothing
