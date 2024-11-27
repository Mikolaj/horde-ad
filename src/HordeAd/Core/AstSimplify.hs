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
  , astNonIndexStep, astIndexStep, astIndexStepS
  , astGatherStep, astGatherStepS
    -- * The simplifying combinators, one for most AST constructors
  , astPair, astLet, astCond, astSumOfList, astSumOfListS
  , astSum, astSumS, astScatter, astScatterS
  , astFromVector, astFromVectorS, astFromVectorX
  , astReplicate, astAppend, astAppendS, astSlice, astSliceS
  , astReverse, astReverseS
  , astTranspose, astTransposeS, astReshape, astReshapeS
  , astCast, astCastS, astFromIntegral, astFromIntegralS
  , astProject1, astProject2, astProjectR, astProjectS, astNestS, astUnNestS
  , astRFromS, astSFromR
  , astPrimalPart, astDualPart
  , astLetHVectorIn, astHApply, astLetFun
    -- * The simplifying bottom-up pass
  , simplifyAst
    -- * The expanding (to gather expressions) bottom-up pass
  , expandAst
    -- * Substitution wrappers
  , substituteAst, substituteAstIndex, substituteAstIxS
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Control.Monad (mapAndUnzipM)
import Data.Functor.Const
import Data.GADT.Compare
import Data.Int (Int64)
import Data.List (dropWhileEnd, elemIndex)
import Data.List.Index (ifoldr)
import Data.Maybe (catMaybes, fromMaybe, isJust)
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Type.Ord (Compare)
import Data.Vector.Generic qualified as V
import GHC.TypeLits
  ( KnownNat
  , Nat
  , OrderingI (..)
  , SomeNat (..)
  , cmpNat
  , fromSNat
  , sameNat
  , someNatVal
  , type (+)
  , type (-)
  , type (<=)
  )
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Types qualified as X (unsafeCoerceRefl)
import Data.Array.Nested
  ( IShR
  , IxS (..)
  , KnownShS (..)
  , KnownShX
  , ListS (..)
  , Rank
  , SMayNat (..)
  , ShR (..)
  , ShS (..)
  , ShX (..)
  , pattern (:$:)
  , pattern (:.$)
  , pattern (:.:)
  , pattern (::$)
  , pattern (:::)
  , pattern ZIR
  , pattern ZIS
  , pattern ZR
  , pattern ZS
  , pattern ZSR
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.Ast
  ( AstBool (AstBoolConst)
  , AstTensor (AstConcrete, AstN1R, AstN1S, AstN2R, AstN2S, AstSumOfListR, AstSumOfListS)
  )
import HordeAd.Core.Ast hiding (AstBool (..), AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

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
  => SimplifyKnobs -> Permutation.PermR -> AstTensor AstMethodLet s (TKR n r)
  -> AstTensor AstMethodLet s (TKR n r)
{-# NOINLINE astTransposeAsGather #-}
astTransposeAsGather knobs perm v =
  let pInt = length perm
  in case someNatVal $ toInteger pInt of
    Just (SomeNat @p _) -> do
      funToVarsIx pInt $ \ (!vars, !ix) ->
        let asts :: AstIndex AstMethodLet p
            asts = Nested.Internal.Shape.ixrPermutePrefix (permInverse perm) ix
        in case cmpNat (Proxy @p) (Proxy @n) of
          EQI -> astGatherKnobsR @p @(n - p) knobs
                                 (Nested.Internal.Shape.shrPermutePrefix perm (shapeAst v)) v
                                 (vars, asts)
          LTI -> astGatherKnobsR @p @(n - p) knobs
                                 (Nested.Internal.Shape.shrPermutePrefix perm (shapeAst v)) v
                                 (vars, asts)
          _ -> error "astTransposeAsGather: permutation longer than rank"
    Nothing -> error "astTransposeAsGather: impossible someNatVal error"

astTransposeAsGatherS
  :: forall perm sh s r p. (GoodScalar r, KnownShS sh, p ~ Rank perm)
  => Permutation.Perm perm -> SimplifyKnobs -> AstTensor AstMethodLet s (TKS sh r)
  -> AstTensor AstMethodLet s (TKS (Permutation.PermutePrefix perm sh) r)
{-# NOINLINE astTransposeAsGatherS #-}
astTransposeAsGatherS perm knobs v =
  withShapeP (drop (sNatValue (Permutation.permRank perm))
              $ shapeT @sh) $ \(Proxy @shd) ->
    gcastWith (unsafeCoerce Refl :: Drop p sh :~: shd) $
    withShapeP (take (sNatValue (Permutation.permRank perm))
                $ shapeT @sh) $ \(Proxy @shp) ->
      gcastWith (unsafeCoerce Refl :: Take p sh :~: shp) $
      withShapeP (backpermutePrefixList (Permutation.permToList' perm)
                                        (shapeT @shp)) $ \(Proxy @sh2) ->
        gcastWith (unsafeCoerce Refl
                   :: Permutation.PermutePrefix perm (Take p sh) :~: sh2) $
        funToVarsIxS @sh2 $ \ (!vars, !ix) ->
          let asts :: AstIxS AstMethodLet (Take p sh)
              asts = ShapedList.permutePrefixIndex (Permutation.permToList' perm) ix
          in gcastWith (unsafeCoerce Refl
                        :: Permutation.PermutePrefix perm sh :~: sh2 ++ Drop p sh) $
             withShapeP (backpermutePrefixList (Permutation.permToList' perm)
                                               (shapeT @shp)
                         ++ drop (sNatValue (Permutation.permRank perm))
                                 (shapeT @sh))
             $ \(Proxy @sh2shp) ->
             gcastWith (unsafeCoerce Refl
                        :: sh2shp :~: sh2 ++ Drop p sh) $
             case Permutation.permRank perm of
               SNat @p2 -> gcastWith (unsafeCoerce Refl :: p2 :~: p) $
                           astGatherKnobsS @sh2 @p @sh knobs v (vars, asts)

-- This generates big terms that don't simplify well,
-- so we keep the AstReshape form until simplification gets stuck.
-- In fact, to simplify the terms we'd need advanced solving of equations
-- in integer arithmetic modulo. Moreover, when solving, we'd need to know
-- the range of all integer variables (taken from shapes) and the floor
-- and minimum/maximum terms (obtained by analysing the embedded Ast term),
-- because many of the emerging terms are not equal to their simplifed
-- forms without this data. Probably we could just subsitute @var `remF` range@
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
  => SimplifyKnobs -> IShR m -> AstTensor AstMethodLet s (TKR p r) -> AstTensor AstMethodLet s (TKR m r)
{-# NOINLINE astReshapeAsGather #-}
astReshapeAsGather knobs shOut v =
  funToVarsIx (lengthShape shOut) $ \ (!vars, !ix) ->
    let shIn = shapeAst v
        asts :: AstIndex AstMethodLet p
        asts = let i = toLinearIdx @m @0 (AstConcrete (FTKS knownShS FTKScalar) . RepN . Nested.sscalar . fromIntegral) shOut ix
               in simplifyAstIndex $ fromLinearIdx (AstConcrete (FTKS knownShS FTKScalar) . RepN . Nested.sscalar . fromIntegral) shIn i
                    -- we generate these, so we simplify
    in astGatherKnobsR @m @0 knobs shOut v (vars, asts)

astReshapeAsGatherS
  :: forall sh sh2 r s. (GoodScalar r, KnownShS sh, KnownShS sh2)
  => SimplifyKnobs -> AstTensor AstMethodLet s (TKS sh r) -> AstTensor AstMethodLet s (TKS sh2 r)
{-# NOINLINE astReshapeAsGatherS #-}
astReshapeAsGatherS knobs v =
  gcastWith (unsafeCoerce Refl :: sh2 ++ '[] :~: sh2) $
  funToVarsIxS @sh2 $ \ (!vars, !ix) ->
    let shIn = knownShS @sh
        shOut = knownShS @sh2
        asts :: AstIxS AstMethodLet sh
        asts = let i :: AstInt AstMethodLet
                   i = ShapedList.toLinearIdx @sh2 @'[] (AstConcrete (FTKS knownShS FTKScalar) . RepN . Nested.sscalar . fromIntegral) shOut ix
               in simplifyAstIxS $ ShapedList.fromLinearIdx (AstConcrete (FTKS knownShS FTKScalar) . RepN . Nested.sscalar . fromIntegral) shIn i
                    -- we generate these, so we simplify
    in gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh) $
       gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[]) $
       withListSh (Proxy @sh) $ \(_ :: IShR p) ->
       gcastWith (unsafeCoerce Refl :: Rank sh :~: p) $
       astGatherKnobsS @sh2 @p @sh knobs v (vars, asts)


-- * Permutation operations

normalizePermutation :: Permutation.PermR -> Permutation.PermR
normalizePermutation perm =
  map fst $ dropWhileEnd (uncurry (==)) $ zip perm [0 ..]

-- A representation of a cycle backpermutation.
backpermCycle :: Int -> Permutation.PermR
backpermCycle 0 = []
backpermCycle 1 = []
backpermCycle n = [k `mod` n | k <- [1 .. n]]

-- A representation of a cycle permutation.
-- TODO: make sure and state if it's reverse to the above and, if not, why.
permCycle :: Int -> Permutation.PermR
permCycle 0 = []
permCycle 1 = []
permCycle n = [k `mod` n | k <- [-1, 0 .. n - 2]]


-- * The combinators for indexing and gather

-- This does a single step of simplification of any non-indexing term
-- (many steps if guaranteed net beneficial). Terms representing integers
-- and and AstBool terms are simplified as much as possible.
astNonIndexStep
  :: (AstSpan s, TensorKind y)
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
astNonIndexStep t = case t of
  Ast.AstScalar u -> Ast.AstScalar $ astNonIndexStep u
  Ast.AstUnScalar u -> Ast.AstUnScalar $ astNonIndexStep u
  Ast.AstPair t1 t2 -> astPair (astNonIndexStep t1) (astNonIndexStep t2)
  Ast.AstProject1 u -> astProject1 u
  Ast.AstProject2 u -> astProject2 u
  Ast.AstVar{} -> t
  Ast.AstPrimalPart v -> astPrimalPart v  -- has to be done sooner or later
  Ast.AstDualPart v -> astDualPart v
  Ast.AstFromPrimal{} -> t
  Ast.AstD{} -> t
  Ast.AstCond a b c -> astCond a b c
  Ast.AstReplicate k v -> astReplicate k v
  Ast.AstBuild1{} -> t
  Ast.AstLet var u v -> astLet var u v
  AstConcrete{} -> t

  Ast.AstMinIndex{} -> t
  Ast.AstMaxIndex{} -> t
  Ast.AstFloor{} -> t
  Ast.AstIota -> t
  AstN1R{} -> t
  AstN2R{} -> t
  Ast.AstR1R{} -> t
  Ast.AstR2R{} -> t
  Ast.AstI2R{} -> t
  AstSumOfListR l -> astSumOfList l
  Ast.AstIndex{} -> t  -- was supposed to be *non*-index
  Ast.AstSum v -> astSum v
  Ast.AstScatter sh v (vars, ix) -> astScatter sh v (vars, ix)
  Ast.AstFromVector l -> astFromVector l
  Ast.AstAppend x y -> astAppend x y
  Ast.AstSlice i k v -> astSlice i k v
  Ast.AstReverse v -> astReverse v
  Ast.AstTranspose perm v -> astTranspose perm v
  Ast.AstReshape sh v -> astReshape sh v
  Ast.AstGather _ v0 (ZR, ix) -> Ast.AstIndex v0 ix
  Ast.AstGather sh v0 (_, ZIR) -> astReplicateN sh v0
  Ast.AstGather{} -> t  -- this is "index" enough
  Ast.AstCast v -> astCast v
  Ast.AstFromIntegral v -> astFromIntegral v
  Ast.AstProjectR l p -> astProjectR l p
  Ast.AstLetHVectorIn vars u v -> astLetHVectorIn vars u v
  Ast.AstRFromS v -> astRFromS v

  Ast.AstMinIndexS{} -> t
  Ast.AstMaxIndexS{} -> t
  Ast.AstFloorS{} -> t
  Ast.AstIotaS -> t
  AstN1S opCode u ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp1 opCode u
      _ -> t
  AstN2S opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp2 opCode u v
      _ -> t
  Ast.AstR1S{} -> t
  Ast.AstR2S{} -> t
  Ast.AstI2S opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstIntegralOp2 opCode u v
      _ -> t
  AstSumOfListS args ->
    case isTensorInt t of
      Just Refl -> foldr1 contractAstPlusOp args
      _ -> t
  Ast.AstIndexS{} -> t  -- was supposed to be *non*-index
  Ast.AstSumS v -> astSumS v
  Ast.AstScatterS v (vars, ix) -> astScatterS v (vars, ix)
  Ast.AstFromVectorS l -> astFromVectorS l
  Ast.AstAppendS x y -> astAppendS x y
  Ast.AstSliceS @i @k v -> astSliceS @i @k v
  Ast.AstReverseS v -> astReverseS v
  Ast.AstTransposeS perm v -> astTransposeS perm v
  Ast.AstReshapeS v -> astReshapeS v
  Ast.AstGatherS @_ @p @sh1 v0 (ZS, ix) ->
    gcastWith (unsafeCoerce Refl :: sh1 :~: Take p sh1 ++ Drop p sh1)
    $ Ast.AstIndexS v0 ix
  Ast.AstGatherS @sh2 @p @sh1 v0 (_ , ZIS) ->
    gcastWith (unsafeCoerce Refl :: Drop p sh1 :~: sh1) $
    astReplicateNS @sh2 @sh1 v0
  Ast.AstGatherS{} -> t  -- this is "index" enough
  Ast.AstCastS v -> astCastS v
  Ast.AstFromIntegralS v -> astFromIntegralS v
  Ast.AstProjectS l p -> astProjectS l p
  Ast.AstNestS v -> astNestS v
  Ast.AstUnNestS v -> astUnNestS v
  Ast.AstSFromR v -> astSFromR v
  _ -> t  -- TODO

astIndexR
  :: forall m n s r.
     (KnownNat m, KnownNat n, GoodScalar r, AstSpan s)
  => AstTensor AstMethodLet s (TKR (m + n) r) -> AstIndex AstMethodLet m -> AstTensor AstMethodLet s (TKR n r)
astIndexR = astIndexKnobsR defaultKnobs

astIndexStep
  :: forall m n s r.
     (KnownNat m, KnownNat n, GoodScalar r, AstSpan s)
  => AstTensor AstMethodLet s (TKR (m + n) r) -> AstIndex AstMethodLet m -> AstTensor AstMethodLet s (TKR n r)
astIndexStep v ix = astIndexKnobsR (defaultKnobs {knobStepOnly = True})
                                   (astNonIndexStep v)
                                   (simplifyAstIndex ix)

astIndexS
  :: forall sh1 sh2 s r.
     ( KnownShS sh1, KnownShS sh2, KnownShS (sh1 ++ sh2)
     , GoodScalar r, AstSpan s )
  => AstTensor AstMethodLet s (TKS (sh1 ++ sh2) r) -> AstIxS AstMethodLet sh1
  -> AstTensor AstMethodLet s (TKS sh2 r)
astIndexS = astIndexKnobsS defaultKnobs

astIndexStepS
  :: forall sh1 sh2 s r.
     ( KnownShS sh1, KnownShS sh2, KnownShS (sh1 ++ sh2)
     , GoodScalar r, AstSpan s )
  => AstTensor AstMethodLet s (TKS (sh1 ++ sh2) r) -> AstIxS AstMethodLet sh1
  -> AstTensor AstMethodLet s (TKS sh2 r)
astIndexStepS v ix = astIndexKnobsS (defaultKnobs {knobStepOnly = True})
                                    (astNonIndexStep v)
                                    (simplifyAstIxS ix)

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
  => SimplifyKnobs -> AstTensor AstMethodLet s (TKR (m + n) r) -> AstIndex AstMethodLet m
  -> AstTensor AstMethodLet s (TKR n r)
astIndexKnobsR knobs (Ast.AstIndex v ix) ZIR =
  astIndexKnobsR knobs v ix  -- no non-indexing constructor yet revealed
astIndexKnobsR _ v0 ZIR = v0
astIndexKnobsR knobs v0 ix@(i1 :.: (rest1 :: AstIndex AstMethodLet m1)) =
 let astIndexRec, astIndex
       :: forall m' n' s'. (KnownNat m', KnownNat n', AstSpan s')
       => AstTensor AstMethodLet s' (TKR (m' + n') r) -> AstIndex AstMethodLet m' -> AstTensor AstMethodLet s' (TKR n' r)
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
       => IShR (m' + n') -> AstTensor AstMethodLet s (TKR (p' + n') r)
       -> (AstVarList m', AstIndex AstMethodLet p')
       -> AstTensor AstMethodLet s (TKR (m' + n') r)
     astGather sh2 v2 (vars2, ix2) =
       if knobStepOnly knobs
       then astGatherKnobsR knobs
                            sh2 (astNonIndexStep v2)
                            (vars2, simplifyAstIndex ix2)
       else astGatherKnobsR knobs sh2 v2 (vars2, ix2)
 in case v0 of
  Ast.AstScalar{} -> Ast.AstIndex v0 ix
  Ast.AstProject1{} -> Ast.AstIndex v0 ix
  Ast.AstProject2{} -> Ast.AstIndex v0 ix
  Ast.AstVar{} -> Ast.AstIndex v0 ix
  Ast.AstPrimalPart{} -> Ast.AstIndex v0 ix  -- must be a NF
  Ast.AstDualPart{} -> Ast.AstIndex v0 ix
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astIndex v ix
  Ast.AstD u u' ->
    shareIx ix $ \ !ix2 -> Ast.AstD (astIndexRec u ix2) (astIndexRec u' ix2)
  Ast.AstCond b v w ->
    shareIx ix $ \ !ix2 -> astCond b (astIndexRec v ix2) (astIndexRec w ix2)
  Ast.AstReplicate @y2 k v | AstConcrete _ (RepN it) <- i1 -> case stensorKind @y2 of
    STKR SNat _ ->
      let i = fromIntegral $ Nested.sunScalar it
      in if 0 <= i && i < sNatValue k
         then astIndex v rest1
         else astReplicate0N (dropShape $ shapeAst v) 0
    _ -> error "astIndexKnobs: type family BuildTensorKind stuck at TKScalar"
{- TODO: this generalization of the above case slows down test 3nestedSumBuild1
   orders of magnitude
  Ast.AstReplicate k v ->
    let len = AstConcrete $ Nested.rscalar $ fromIntegral k
        zero = astReplicate0N (dropShape $ shapeAst v) 0
    in case simplifyAstBool $ Ast.AstB2 AndOp (Ast.AstRel LeqOp 0 i1)
                                              (Ast.AstRel LsOp i1 len) of
      AstBoolConst b -> if b then astIndex v rest1 else zero
      bExpr -> astCond bExpr (astIndex v rest1) zero -}
  Ast.AstReplicate @y2 _k v -> case stensorKind @y2 of
    STKR{} -> astIndex v rest1
    _ -> error "astIndexKnobs: type family BuildTensorKind stuck at TKScalar"
  Ast.AstBuild1 @y2 _snat (var2, v) -> case stensorKind @y2 of
    STKR{} -> astIndex (astLet var2 i1 v) rest1
    _ -> error "astIndexKnobs: type family BuildTensorKind stuck at TKScalar"
  Ast.AstLet var u v -> astLet var u (astIndexRec v ix)

  Ast.AstMinIndex v -> Ast.AstMinIndex $ astIndexKnobsR knobs v ix
  Ast.AstMaxIndex v -> Ast.AstMaxIndex $ astIndexKnobsR knobs v ix
  Ast.AstFloor v -> Ast.AstFloor $ astIndexKnobsR knobs v ix
  Ast.AstIota | AstConcrete{} <- i1 -> case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> astFromIntegral $ astRFromS i1
    _ -> error "astIndexKnobsR: rank not 0"
  Ast.AstIota -> Ast.AstIndex v0 ix
  AstN1R opCode u ->
    shareIx ix $ \ !ix2 -> AstN1R opCode (astIndexRec u ix2)
  AstN2R opCode u v ->
    shareIx ix $ \ !ix2 -> AstN2R opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstR1R opCode u ->
    shareIx ix
    $ \ !ix2 -> Ast.AstR1R opCode (astIndexRec u ix2)
  Ast.AstR2R opCode u v ->
    shareIx ix
    $ \ !ix2 -> Ast.AstR2R opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstI2R opCode u v ->
    shareIx ix
    $ \ !ix2 -> Ast.AstI2R opCode (astIndexRec u ix2) (astIndexRec v ix2)
  AstSumOfListR args ->
    shareIx ix $ \ !ix2 -> astSumOfList (map (`astIndexRec` ix2) args)
  Ast.AstIndex v ix2 ->
    astIndex v (appendIndex ix2 ix)
  Ast.AstSum v ->  -- almost neutral; transposition is likely to fuse away
    let perm3 = backpermCycle $ valueOf @m + 1
    in astSum $ astIndex (astTranspose perm3 v) ix
  Ast.AstScatter @_ @n7 (_ :$: sh)
                 v (vars, AstIntVar var5 :.: (ix2 :: AstIndex AstMethodLet p71))
    | AstIntVar var6 <- i1, var6 == var5 ->
        gcastWith (unsafeCoerce Refl :: m1 + n :~: p71 + n7) $
        astIndex (astScatter sh v (vars, ix2)) rest1
  Ast.AstScatter @_ @n7 (_ :$: sh)
                 v (vars, AstConcrete _ i5 :.: (ix2 :: AstIndex AstMethodLet p71))
    | AstConcrete _ i6 <- i1 ->
        gcastWith (unsafeCoerce Refl :: m1 + n :~: p71 + n7) $
        if i6 == i5
        then astIndex (astScatter sh v (vars, ix2)) rest1
        else astReplicate0N (dropShape @m1 sh) 0
  -- AstScatter sh v (vars2, ZIR) ->
  --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZIR)
  Ast.AstScatter{} ->  -- normal form
    Ast.AstIndex v0 ix
  Ast.AstFromVector l | AstConcrete _ (RepN it) <- i1 ->
    let i = fromIntegral $ Nested.sunScalar it
    in if 0 <= i && i < length l
       then astIndex (l V.! i) rest1
       else astReplicate0N (dropShape $ shapeAst v0) 0
  Ast.AstFromVector{} | ZIR <- rest1 ->  -- normal form
    Ast.AstIndex v0 ix
  Ast.AstFromVector l ->
    shareIx rest1 $ \ !ix2 ->
      Ast.AstIndex (astFromVector $ V.map (`astIndexRec` ix2) l)
                   (singletonIndex i1)
  Ast.AstAppend u v ->
    let ulen = AstConcrete (FTKS knownShS FTKScalar)
               $ RepN $ Nested.sscalar $ fromIntegral $ lengthAst u
        ix2 = simplifyAstInt (AstN2S MinusOp i1 ulen) :.: rest1
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
    astIndex v (Nested.Internal.Shape.ixrPermutePrefix (permInverse perm) ix)
  Ast.AstTranspose perm v ->
    astIndex (astTransposeAsGather knobs perm v) ix
  Ast.AstReshape sh v ->
    astIndex (astReshapeAsGather knobs sh v) ix
  Ast.AstGather _sh v (ZR, ix2) -> astIndex v (appendIndex ix2 ix)
  Ast.AstGather @_ @n7 (_ :$: sh') v (var2 ::: (vars :: AstVarList m71), ix2) ->
    let w :: AstTensor AstMethodLet s (TKR (m1 + n) r)
        w = gcastWith (unsafeCoerce Refl :: m1 + n :~: m71 + n7) $
            astGather sh' v (vars, ix2)
    in astLet var2 i1 $ astIndex w rest1
  Ast.AstGather{} ->
    error "astIndex: AstGather: impossible pattern needlessly required"
  Ast.AstCast t -> astCast $ astIndexKnobsR knobs t ix
  Ast.AstFromIntegral v -> astFromIntegral $ astIndexKnobsR knobs v ix
  AstConcrete _ t ->
    let unConst :: AstInt AstMethodLet -> Maybe [Nested.Shaped '[] Int64]
                -> Maybe [Nested.Shaped '[] Int64]
        unConst (AstConcrete _ (RepN i)) (Just l) = Just $ i : l
        unConst _ _ = Nothing
    in case foldr unConst (Just []) ix of
      Just ixInt ->
        let u = tindexZR (unRepN t) $ listToIndex
                $ map Nested.sunScalar ixInt
        in AstConcrete (FTKR (Nested.rshape u) FTKScalar) $ RepN u
          -- TODO: we'd need mapM for Index to keep this rank-typed
      Nothing -> Ast.AstIndex v0 ix
  Ast.AstProjectR{} -> Ast.AstIndex v0 ix
  {- TODO: this is not really helping:
  Ast.AstProjectR Ast.AstVar{} _ -> Ast.AstIndex v0 ix
  Ast.AstProjectR (Ast.AstProject1 Ast.AstVar{}) _ -> Ast.AstIndex v0 ix
  Ast.AstProjectR (Ast.AstProject2 Ast.AstVar{}) _ -> Ast.AstIndex v0 ix
  Ast.AstProjectR l p ->
    fun1DToAst (shapeAstHVector l) $ \ !vars !asts ->
      let lp = fromDynamicR (\sh -> AstRanked $ astReplicate0N sh 0) (asts V.! p)
      in astLetHVectorIn vars l (astIndexRec (unAstRanked lp) ix) -}
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars l (astIndexRec v ix)
  Ast.AstRFromS @sh t ->
    let (takeSh, dropSh) = splitAt (valueOf @m) (shapeT @sh)
    in withShapeP takeSh $ \(Proxy @p_take) ->
       withShapeP dropSh $ \(Proxy @p_drop) ->
       gcastWith (unsafeCoerce Refl :: sh :~: p_take ++ p_drop) $
       gcastWith (unsafeCoerce Refl :: Rank p_drop :~: n) $
       astRFromS $ astIndexKnobsS @p_take @p_drop knobs
                                  t (ShapedList.listToIndex $ indexToList ix)

  Ast.AstApply{} -> Ast.AstIndex v0 ix

astIndexKnobsS
  :: forall shm shn s r.
     ( KnownShS shm, KnownShS shn, KnownShS (shm ++ shn)
     , GoodScalar r, AstSpan s )
  => SimplifyKnobs -> AstTensor AstMethodLet s (TKS (shm ++ shn) r) -> AstIxS AstMethodLet shm
  -> AstTensor AstMethodLet s (TKS shn r)
astIndexKnobsS knobs (Ast.AstIndexS v ix) ZIS = astIndexKnobsS knobs v ix
astIndexKnobsS _ v0 ZIS = v0
astIndexKnobsS knobs v0 ix@((:.$) @in1 i1 (rest1 :: AstIxS AstMethodLet shm1)) | Dict <- sixKnown rest1 =
  let astIndexRec, astIndex
        :: forall shm' shn' s'.
           ( KnownShS shm', KnownShS shn', KnownShS (shm' ++ shn')
           , AstSpan s' )
        => AstTensor AstMethodLet s' (TKS (shm' ++ shn') r) -> AstIxS AstMethodLet shm'
        -> AstTensor AstMethodLet s' (TKS shn' r)
      astIndexRec v2 ZIS = v2
      astIndexRec v2 ix2 = if knobStepOnly knobs
                           then Ast.AstIndexS v2 ix2
                           else astIndexKnobsS knobs v2 ix2
      astIndex v2 ix2 = if knobStepOnly knobs
                        then astIndexKnobsS knobs
                                            (astNonIndexStep v2)
                                            (simplifyAstIxS ix2)
                        else astIndexKnobsS knobs v2 ix2
      astGather
        :: forall shm' shn' p'.
           ( KnownShS shm', KnownShS shn', KnownNat p'
           , KnownShS (Take p' shm'), KnownShS (Drop p' shm')
           , KnownShS (shn' ++ Drop p' shm') )
       => AstTensor AstMethodLet s (TKS shm' r)
        -> (AstVarListS shn', AstIxS AstMethodLet (Take p' shm'))
        -> AstTensor AstMethodLet s (TKS (shn' ++ Drop p' shm') r)
      astGather v2 (vars2, ix2) =
        if knobStepOnly knobs
        then astGatherKnobsS knobs
                             (astNonIndexStep v2)
                             (vars2, simplifyAstIxS ix2)
        else astGatherKnobsS knobs v2 (vars2, ix2)
 in case v0 of
  Ast.AstProject1{} -> Ast.AstIndexS v0 ix
  Ast.AstProject2{} -> Ast.AstIndexS v0 ix
  Ast.AstVar{} -> Ast.AstIndexS v0 ix
  Ast.AstPrimalPart{} -> Ast.AstIndexS v0 ix  -- must be a NF
  Ast.AstDualPart{} -> Ast.AstIndexS v0 ix
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astIndex v ix
  Ast.AstD u u' ->
    shareIxS ix $ \ !ix2 -> Ast.AstD (astIndexRec u ix2) (astIndexRec u' ix2)
  Ast.AstCond b v w ->
    shareIxS ix $ \ !ix2 -> astCond b (astIndexRec v ix2) (astIndexRec w ix2)
  Ast.AstReplicate @y2 _snat v -> case stensorKind @y2 of
    STKS sh _ -> withKnownShS sh $ astIndex v rest1
    _ -> error "astIndexKnobsS: type family BuildTensorKind stuck at TKScalar"
  Ast.AstBuild1 @y2 _snat (var2, v) -> case stensorKind @y2 of
    STKS sh _ -> withKnownShS sh $
      withListSh (Proxy @(shm1 ++ shn)) $ \_ ->
        astIndex (astSFromR @(shm1 ++ shn) $ astLet var2 i1 $ astRFromS v)
                 rest1
        -- this uses astLet, because the index integers are ranked
    _ -> error "astIndexKnobsS: type family BuildTensorKind stuck at TKScalar"
  Ast.AstLet var u v -> astLet var u (astIndexRec v ix)

  Ast.AstMinIndexS @shz @n1 v ->
    withShapeP (drop 1 (shapeT @shn)
                   ++ [last (shapeT @shz)]) $ \(Proxy @shd) ->
      gcastWith (unsafeCoerce Refl
                 :: Drop 1 shn ++ '[Last shz] :~: shd) $
      withSNat (shapeT @shn !! 0) $ \(SNat @i0shn) ->
        gcastWith (unsafeCoerce Refl :: Permutation.Index 0 shn :~: i0shn) $
        gcastWith (unsafeCoerce Refl
                   :: Permutation.Index 0 shn ': Drop 1 shn :~: shn) $
        gcastWith (unsafeCoerce Refl
                   :: Init (shn ++ '[Last shz]) :~: shn) $
        gcastWith (unsafeCoerce Refl
                   :: shm ++ (shn ++ '[Last shz]) :~: n1 ': shz) $
        Ast.AstMinIndexS @(Drop 1 shn ++ '[Last shz]) @(Permutation.Index 0 shn)
        $ astIndexKnobsS @shm @(shn ++ '[Last shz]) knobs v ix
  Ast.AstMaxIndexS @shz @n1 v ->
    withShapeP (drop 1 (shapeT @shn)
                   ++ [last (shapeT @shz)]) $ \(Proxy @shd) ->
      gcastWith (unsafeCoerce Refl
                 :: Drop 1 shn ++ '[Last shz] :~: shd) $
      withSNat (shapeT @shn !! 0) $ \(SNat @i0shn) ->
        gcastWith (unsafeCoerce Refl :: Permutation.Index 0 shn :~: i0shn) $
        gcastWith (unsafeCoerce Refl
                   :: Permutation.Index 0 shn ': Drop 1 shn :~: shn) $
        gcastWith (unsafeCoerce Refl
                   :: Init (shn ++ '[Last shz]) :~: shn) $
        gcastWith (unsafeCoerce Refl
                   :: shm ++ (shn ++ '[Last shz]) :~: n1 ': shz) $
        Ast.AstMaxIndexS @(Drop 1 shn ++ '[Last shz]) @(Permutation.Index 0 shn)
        $ astIndexKnobsS @shm @(shn ++ '[Last shz]) knobs v ix
  Ast.AstFloorS v -> Ast.AstFloorS $ astIndexKnobsS knobs v ix
  Ast.AstIotaS | AstConcrete{} <- i1 -> case sameShape @shn @'[] of
    Just Refl -> astFromIntegralS i1
    _ -> error "astIndexKnobsS: shape not []"
  Ast.AstIotaS -> Ast.AstIndexS v0 ix
  AstN1S opCode u ->
    shareIxS ix $ \ !ix2 -> AstN1S opCode (astIndexRec u ix2)
  AstN2S opCode u v ->
    shareIxS ix $ \ !ix2 -> AstN2S opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstR1S opCode u ->
    shareIxS ix
    $ \ !ix2 -> Ast.AstR1S opCode (astIndexRec u ix2)
  Ast.AstR2S opCode u v ->
    shareIxS ix
    $ \ !ix2 -> Ast.AstR2S opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstI2S opCode u v ->
    shareIxS ix
    $ \ !ix2 -> Ast.AstI2S opCode (astIndexRec u ix2) (astIndexRec v ix2)
  AstSumOfListS args ->
    shareIxS ix $ \ !ix2 -> astSumOfListS (map (`astIndexRec` ix2) args)
  Ast.AstIndexS v (ix2 :: AstIxS AstMethodLet sh4) ->
    gcastWith (unsafeCoerce Refl
               :: (sh4 ++ shm) ++ shn :~: sh4 ++ (shm ++ shn)) $
    withShapeP (shapeT @sh4 ++ shapeT @shm) $ \(Proxy @sh41) ->
      gcastWith (unsafeCoerce Refl :: sh4 ++ shm :~: sh41) $
      astIndexS v (ShapedList.appendIndex ix2 ix)
  Ast.AstSumS @n1 v ->
    let perm3 = backpermCycle $ length (shapeT @shm) + 1
    in withShapeP (shapeT @shm
                   ++ (valueOf @n1 : shapeT @shn)) $ \(Proxy @sm1n) ->
      gcastWith (unsafeCoerce Refl :: shm ++ (n1 : shn) :~: sm1n) $
      withSNat (1 + length (shapeT @shn)
                + length (shapeT @shm)) $ \(SNat @r1mn) ->
        gcastWith (unsafeCoerce Refl :: Rank (n1 : shm ++ shn) :~: r1mn) $
        Permutation.permFromList perm3 $ \(perm :: Permutation.Perm perm3P) ->
          gcastWith (unsafeCoerce Refl
                     :: Compare (Rank perm3P) (Rank (n1 : shm ++ shn))
                        :~: LT) $
          gcastWith (unsafeCoerce Refl
                     :: Permutation.PermutePrefix perm3P (n1 : (shm ++ shn))
                        :~: shm ++ (n1 : shn)) $
          trustMeThisIsAPermutation @perm3P $
          astSumS $ astIndex @shm @(n1 : shn)
                             (astTransposeS @perm3P @(n1 : shm ++ shn) perm v)
                             ix
-- TODO:
--  Ast.AstScatterS @sh2 @p7 @sh7
--                  v (vars, AstIntVar var5 ::$ (ix2 :: AstIxS p71))
--    | AstIntVar var6 <- i1, var6 == var5 ->
--        gcastWith (unsafeCoerce Refl
--                   :: shm1 ++ shn :~: p71 ++ Drop p7 sh7) $
--        astIndex (astScatterS @_ @_ @sh7 v (vars, ix2)) rest1
--  Ast.AstScatter @_ @n7 (_ :$: sh)
--                 v (vars, AstConcrete i5 :.: (ix2 :: AstIndex p71))
--    | AstConcrete i6 <- i1 ->
--        gcastWith (unsafeCoerce Refl :: m1 + n :~: p71 + n7) $
--        if i6 == i5
--        then astIndex (astScatter sh v (vars, ix2)) rest1
--        else astIndex (astReplicate0N @(m1 + n) sh 0) rest1
  -- AstScatter sh v (vars2, ZIR) ->
  --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZIR)
  Ast.AstScatterS{} ->  -- normal form
    Ast.AstIndexS v0 ix
  Ast.AstFromVectorS l | AstConcrete _ it <- i1 ->
    let i = fromIntegral $ Nested.sunScalar $ unRepN it
    in if 0 <= i && i < length l
       then astIndex (l V.! i) rest1
       else astReplicate0NS 0
  Ast.AstFromVectorS{} | ZIS <- rest1 ->  -- normal form
    Ast.AstIndexS v0 ix
  Ast.AstFromVectorS l ->
    shareIxS rest1 $ \ !ix2 ->
      Ast.AstIndexS @'[in1] @shn (astFromVectorS $ V.map (`astIndexRec` ix2) l)
                    (ShapedList.singletonIndex i1)
  Ast.AstAppendS @_ @m u v ->
    let ulen = AstConcrete (FTKS knownShS FTKScalar)
               $ RepN $ Nested.sscalar $ fromIntegral (valueOf @m :: Int)
        ix1 = i1 :.$ rest1
        ix2 = simplifyAstInt (AstN2S MinusOp i1 ulen) :.$ rest1
    in case simplifyAstBool $ Ast.AstRel LsOp i1 ulen of
      AstBoolConst b -> if b then astIndex u ix1 else astIndex v ix2
      bExpr -> astCond bExpr (astIndexRec u ix1) (astIndexRec v ix2)
  Ast.AstSliceS @i v ->
    let ii = simplifyAstInt (i1 + fromIntegral (valueOf @i :: Int))
      -- we generate this index, so we simplify on the spot
    in astIndex v (ii :.$ rest1)
  Ast.AstReverseS v ->
    let iRev = simplifyAstInt (fromIntegral (valueOf @in1 - 1 :: Int) - i1)
      -- we generate this index, so we simplify on the spot
    in astIndex v (iRev :.$ rest1)
  Ast.AstTransposeS @perm perm v
    | rankPerm <- Permutation.permRank perm
    , length (shapeT @shm) < sNatValue rankPerm ->
      astIndex (astTransposeAsGatherS @perm perm knobs v) ix
  Ast.AstTransposeS @perm @sh2 perm v ->
    withShapeP
      (permutePrefixList (Permutation.permToList' perm)
                         (shapeT @shm)) $ \(Proxy @shmPerm) ->
        gcastWith (unsafeCoerce Refl :: shm :~: Permutation.PermutePrefix perm shmPerm) $
        let ix2 :: AstIxS AstMethodLet shmPerm = unsafeCoerce $
              Nested.Internal.Shape.ixsPermutePrefix perm ix
        in gcastWith (unsafeCoerce Refl :: sh2 :~: shmPerm ++ shn) $
           astIndex @shmPerm v ix2
  Ast.AstReshapeS v ->
    astIndex (astReshapeAsGatherS knobs v) ix
  Ast.AstGatherS @_ @p @sh v (ZS, ix2) ->
    withShapeP (shapeT @(Take p sh) ++ shapeT @shm)
    $ \(Proxy @sh1n) ->
      gcastWith (unsafeCoerce Refl :: (Take p sh ++ shm :~: sh1n)) $
      gcastWith (unsafeCoerce Refl :: Take p sh ++ shm ++ shn :~: sh) $
        -- TODO: why is this needed? if it's true (it is), GHC should know it
      astIndex v (ShapedList.appendIndex ix2 ix)
  Ast.AstGatherS v (Const var2 ::$ (vars :: AstVarListS shm71), ix2) | Dict <- slistKnown vars ->
    withListSh (Proxy @shn) $ \_ ->
      withShapeP (shapeT @shm1 ++ shapeT @shn) $ \(Proxy @sh1n) ->
        gcastWith (unsafeCoerce Refl :: shm1 ++ shn :~: sh1n) $
        let w :: AstTensor AstMethodLet s (TKS (shm1 ++ shn) r)
            w = astGather v (vars, ix2)
        in astSFromR $ astLet var2 i1 $ astRFromS $ astIndexS @shm1 @shn w rest1
      -- this uses astLet, because the index integers are ranked
  Ast.AstCastS t -> astCastS $ astIndexKnobsS knobs t ix
  Ast.AstFromIntegralS v -> astFromIntegralS $ astIndexKnobsS knobs v ix
  AstConcrete _ t ->
    let unConst :: AstInt AstMethodLet -> Maybe [Nested.Shaped '[] Int64]
                -> Maybe [Nested.Shaped '[] Int64]
        unConst (AstConcrete _ (RepN i)) (Just l) = Just $ i : l
        unConst _ _ = Nothing
    in case foldr unConst (Just []) ix of
      Just ixInt -> AstConcrete (FTKS knownShS FTKScalar)
                    $ RepN $ tindexZS (unRepN t)
                    $ ShapedList.listToIndex @shm $ map Nested.sunScalar ixInt
        -- TODO: we'd need mapM for Index to keep this rank-typed
      Nothing -> Ast.AstIndexS v0 ix
  Ast.AstProjectS{} -> Ast.AstIndexS v0 ix
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars l (astIndexRec v ix)
-- TODO: generalize AstIndexS?  Ast.AstNestS v -> astNestS (astIndexRec v ix)
-- TODO: hard:  Ast.AstUnNestS v -> astUnNestS (astIndexRec v ix)
  Ast.AstUnNestS _ -> Ast.AstIndexS v0 ix
  Ast.AstSFromR t ->
    withListSh (Proxy @shn) $ \_ ->
    withListSh (Proxy @shm) $ \_ ->
      gcastWith (unsafeCoerce Refl
                 :: Rank shm + Rank shn :~: Rank (shm ++ shn)) $
      astSFromR $ astIndexKnobsR knobs t (ShapedList.shapedToIndex ix)

  Ast.AstApply{} -> Ast.AstIndexS v0 ix

-- TODO: compared to tletIx, it adds many lets, not one, but does not
-- create other (and non-simplified!) big terms and also uses astIsSmall,
-- so it's probably more efficient. Use this instead of tletIx/sletIx
-- or design something even better.
shareIx :: (KnownNat n, GoodScalar r, KnownNat m)
        => AstIndex AstMethodLet n -> (AstIndex AstMethodLet n -> AstTensor AstMethodLet s (TKR m r))
        -> AstTensor AstMethodLet s (TKR m r)
{-# NOINLINE shareIx #-}
shareIx ix f = unsafePerformIO $ do
  let shareI :: AstInt AstMethodLet -> IO (Maybe (IntVarName, AstInt AstMethodLet), AstInt AstMethodLet)
      shareI i | astIsSmall True i = return (Nothing, i)
      shareI i = funToAstIntVarIO $ \ (!varFresh, !astVarFresh) ->
                   (Just (varFresh, i), astVarFresh)
  (bindings, ix2) <- mapAndUnzipM shareI (indexToList ix)
  return $! foldr (uncurry Ast.AstLet) (f $ listToIndex ix2)
                                       (catMaybes bindings)

shareIxS :: -- (KnownShS shn, KnownShS shm)
            AstIxS AstMethodLet shn -> (AstIxS AstMethodLet shn -> AstTensor AstMethodLet s (TKS shm r))
         -> AstTensor AstMethodLet s (TKS shm r)
{-# NOINLINE shareIxS #-}
shareIxS ix f = f ix  -- TODO

astGatherR
  :: forall m n p s r.
     (KnownNat m, KnownNat p, KnownNat n, GoodScalar r, AstSpan s)
  => IShR (m + n) -> AstTensor AstMethodLet s (TKR (p + n) r) -> (AstVarList m, AstIndex AstMethodLet p)
  -> AstTensor AstMethodLet s (TKR (m + n) r)
astGatherR = astGatherKnobsR defaultKnobs

astGatherS
  :: forall sh2 p sh s r.
     ( GoodScalar r, KnownShS sh, KnownShS sh2, KnownNat p
     , KnownShS (Take p sh), KnownShS (Drop p sh)
     , KnownShS (sh2 ++ Drop p sh) )
  => AstTensor AstMethodLet s (TKS sh r)
  -> (AstVarListS sh2, AstIxS AstMethodLet (Take p sh))
  -> AstTensor AstMethodLet s (TKS (sh2 ++ Drop p sh) r)
astGatherS = astGatherKnobsS defaultKnobs

astGatherStep
  :: forall m n p s r.
     (KnownNat m, KnownNat p, KnownNat n, GoodScalar r, AstSpan s)
  => IShR (m + n) -> AstTensor AstMethodLet s (TKR (p + n) r) -> (AstVarList m, AstIndex AstMethodLet p)
  -> AstTensor AstMethodLet s (TKR (m + n) r)
astGatherStep sh v (vars, ix) =
  astGatherKnobsR (defaultKnobs {knobStepOnly = True})
                  sh (astNonIndexStep v)
                  (vars, simplifyAstIndex ix)

astGatherStepS
  :: forall sh2 p sh s r.
     ( KnownShS sh, KnownShS sh2, KnownNat p, GoodScalar r, AstSpan s
     , KnownShS (Take p sh), KnownShS (Drop p sh)
     , KnownShS (sh2 ++ Drop p sh) )
  => AstTensor AstMethodLet s (TKS sh r)
  -> (AstVarListS sh2, AstIxS AstMethodLet (Take p sh))
  -> AstTensor AstMethodLet s (TKS (sh2 ++ Drop p sh) r)
-- TODO: this probably needs an extra condition similar to kN == vkN below
--astGatherStepS v (AstVarName varId ::$ ZSS, AstIntVarS varId2 :.$ ZIS)
--  | varId == varId2 = ...
astGatherStepS v (vars, ix) =
  astGatherKnobsS (defaultKnobs {knobStepOnly = True})
                  (astNonIndexStep v)
                  (vars, simplifyAstIxS ix)

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
  => SimplifyKnobs -> IShR (m + n) -> AstTensor AstMethodLet s (TKR (p + n) r)
  -> (AstVarList m, AstIndex AstMethodLet p)
  -> AstTensor AstMethodLet s (TKR (m + n) r)
astGatherKnobsR knobs sh0 v0 (vars0, ix0) =
  case (sh0, (vars0, ix0)) of
    _ | any (`varNameInAst` v0) vars0 ->
      error $ "astGather: gather vars in v0: "
              ++ show (vars0, v0)
    (_, (ZR, _)) -> astIndex v0 ix0
    (sh, (_, ZIR)) -> if knobExpand knobs
                      then Ast.AstGather sh0 v0 (vars0, ix0)
                      else astReplicateN sh v0
    (k :$: sh', (var ::: vars, i1 :.: rest1)) ->
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
         | varInIndex (varNameToAstVarId var) ix0 ->
           astGatherCase sh0 v0 (vars0, ix0)
         | otherwise ->
           if knobExpand knobs
           then Ast.AstGather sh0 v0 (vars0, ix0)
           else case knownShR sh' of
             Dict -> withSNat k $ \snat ->
               astReplicate snat (astGatherKnobsR knobs sh' v0 (vars, ix0))
       where
        (restN, iN) = unsnocIndex1 ix0
        (varsN, varN) = unsnocSized1 vars0
    _ ->
      error "astGather: impossible pattern needlessly required"
 where
  astIndex :: forall m' n' s'. (KnownNat m', KnownNat n', AstSpan s')
           => AstTensor AstMethodLet s' (TKR (m' + n') r) -> AstIndex AstMethodLet m'
           -> AstTensor AstMethodLet s' (TKR n' r)
  astIndex v2 ix2 = if knobStepOnly knobs
                    then astIndexKnobsR knobs
                                        (astNonIndexStep v2)
                                        (simplifyAstIndex ix2)
                    else astIndexKnobsR knobs v2 ix2
  astGatherRec, astGather
    :: forall m' n' p' s' r'.
       (KnownNat m', KnownNat p', KnownNat n', AstSpan s', GoodScalar r')
    => IShR (m' + n') -> AstTensor AstMethodLet s' (TKR (p' + n') r')
    -> (AstVarList m', AstIndex AstMethodLet p')
    -> AstTensor AstMethodLet s' (TKR (m' + n') r')
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
    => IShR (m' + n') -> AstTensor AstMethodLet s (TKR (p' + n') r')
    -> (AstVarList m', AstIndex AstMethodLet p')
    -> AstTensor AstMethodLet s (TKR (m' + n') r')
  astGatherCase sh4 v4 (_, ZIR) = astReplicateN sh4 v4  -- not really possible
  astGatherCase sh4 v4 ( vars4
                       , ix4@(i4 :.: (rest4 :: AstIndex AstMethodLet p1')) ) = case v4 of
    Ast.AstScalar{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstProject1{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstProject2{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstVar{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstPrimalPart{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstDualPart{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astGather sh4 v (vars4, ix4)
    Ast.AstD u u' ->
      -- Term ix4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use tlet.
      -- Also, the sharing would be dissolved by the substitution, anyway,
      -- and the same subsitution would be unsound with sharing.
      funToVarsIx (valueOf @m') $ \ (!varsFresh, !ixFresh) ->
        -- This subst doesn't currently break sharing, because it's a rename.
        let subst i =
              foldr (\(i2, var2) v2 ->
                       substituteAst i2 var2 v2)
                    i
                    (zipSized (indexToSized ixFresh) vars4)
            ix5 = fmap subst ix4
        in Ast.AstD (astGatherRec sh4 u (vars4, ix4))
                    (astGatherRec sh4 u' (varsFresh, ix5))
    Ast.AstCond b v w -> astCond b (astGather sh4 v (vars4, ix4))
                                   (astGather sh4 w (vars4, ix4))
    Ast.AstReplicate @y2 snat v | AstConcrete _ it <- i4 -> case stensorKind @y2 of
      STKR{} ->
        let i = fromIntegral $ Nested.sunScalar $ unRepN $ it
        in if 0 <= i && i < sNatValue snat
           then astGather sh4 v (vars4, rest4)
           else astReplicate0N sh4 0
      _ -> error "astGatherCase: type family BuildTensorKind stuck at TKScalar"
    Ast.AstReplicate @y2 _ v -> case stensorKind @y2 of
      STKR{} -> astGather sh4 v (vars4, rest4)
      _ -> error "astGatherCase: type family BuildTensorKind stuck at TKScalar"
    Ast.AstBuild1{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstLet var u v -> astLet var u (astGatherCase sh4 v (vars4, ix4))

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
    Ast.AstIota | AstConcrete{} <- i4 -> case sameNat (Proxy @p') (Proxy @1) of
      Just Refl -> astReplicate0NT sh4 $ astFromIntegral $ astRFromS i4
      _ -> error "astGather: AstIota: impossible pattern needlessly required"
    Ast.AstIota ->  -- probably nothing can be simplified; a normal form
      Ast.AstGather sh4 v4 (vars4, ix4)
    AstN1R opCode v | not (isVar v) ->
      AstN1R opCode (astGatherRec sh4 v (vars4, ix4))
    AstN1R{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    AstN2R{} -> Ast.AstGather sh4 v4 (vars4, ix4)
      -- Going inside AstN2R usually makes the term more expensive to interpret
      -- and reverting this transformation requires comparing two arguments,
      -- so it's not practical.
    Ast.AstR1R opCode v | not (isVar v) ->
      Ast.AstR1R opCode (astGatherRec sh4 v (vars4, ix4))
    Ast.AstR1R{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstR2R{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstI2R{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    AstSumOfListR{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstIndex v2 ix2 -> case (v2, ix2) of
      (Ast.AstFromVector{}, i2 :.: ZIR) -> astGather sh4 v2 (vars4, i2 :.: ix4)
      _ ->  -- AstVar, AstConcrete
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
                   v (vars, AstIntVar var5 :.: (ix2 :: AstIndex AstMethodLet p71))
      | AstIntVar var6 <- i4, var6 == var5 ->
          gcastWith (unsafeCoerce Refl :: p1' + n' :~: p71 + n7) $
          astGather sh4 (astScatter sh v (vars, ix2))
                        (vars4, rest4)
    Ast.AstScatter @_ @n7 (_ :$: sh)
                   v (vars, AstConcrete _ i5 :.: (ix2 :: AstIndex AstMethodLet p71))
      | AstConcrete _ i6 <- i4 ->
          gcastWith (unsafeCoerce Refl :: p1' + n' :~: p71 + n7) $
          if i6 == i5
          then astGather sh4 (astScatter sh v (vars, ix2)) (vars4, rest4)
          else astReplicate0N sh4 0
    Ast.AstScatter{} ->  -- normal form
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstFromVector l | AstConcrete _ it <- i4 ->
      let i = fromIntegral $ Nested.sunScalar $ unRepN it
      in if 0 <= i && i < length l
         then astGather sh4 (l V.! i) (vars4, rest4)
         else astReplicate0N sh4 0
    Ast.AstFromVector{} | gatherFromNF vars4 ix4 ->  -- normal form
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstFromVector l ->
      -- Term rest4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use tlet.
      funToVarsIx (valueOf @m') $ \ (!varsFresh, !ixFresh) ->
        let f v = astGatherRec sh4 v (vars4, rest4)
            -- This subst doesn't currently break sharing because it's a rename.
            subst i =
              foldr (\(i2, var2) v2 ->
                      substituteAst i2 var2 v2)
                    i
                    (zipSized (indexToSized ixFresh) vars4)
            i5 = subst i4
       in astGather sh4 (astFromVector $ V.map f l) (varsFresh, i5 :.: ixFresh)
    Ast.AstAppend u v ->
      let ulen = AstConcrete (FTKS knownShS FTKScalar)
                 $ RepN $ Nested.sscalar $ fromIntegral $ lengthAst u
          iu = simplifyAstInt (AstN2S MinusOp i4 ulen)
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
                        (zipSized (indexToSized ixFresh) vars4)
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
      astGather sh4 v (vars4, Nested.Internal.Shape.ixrPermutePrefix (permInverse perm) ix4)
    Ast.AstTranspose perm v ->
      if knobExpand knobs
      then astGather sh4 (astTransposeAsGather knobs perm v) (vars4, ix4)
      else Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstReshape sh v ->
      if knobExpand knobs
      then astGather sh4 (astReshapeAsGather knobs sh v) (vars4, ix4)
      else Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstGather @m2 @n2 _sh2 v2 (vars2, ix2) ->
      -- Term ix4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use tlet.
      --
      -- Independently, we need to insert lets to each index element,
      -- bloating the term. TODO: would going via a rank 1 vector,
      -- as in tletIx help or would we need to switch indexes to vector
      -- altogether (terrible for user comfort, especially wrt typing).
      let substLet :: AstIndex AstMethodLet m7 -> AstVarList m7 -> AstInt AstMethodLet -> AstInt AstMethodLet
          substLet ix vars i =
            simplifyAstInt  -- we generate the index, so we simplify on the spot
            $ foldr (uncurry astLetInt) i
                    (zipSized vars (indexToSized ix))
          composedGather :: p' <= m2 => AstTensor AstMethodLet s (TKR (m' + n') r')
          composedGather =
            let (vars2p, vars22) = splitAt_Sized @p' @(m2 - p') vars2
                ix22 = fmap (substLet ix4 vars2p) ix2
            in gcastWith (unsafeCoerce Refl :: m2 + n2 - p' :~: n')
               $ astGather sh4 v2 (appendSized vars4 vars22, ix22)
          assimilatedGather :: m2 <= p' => AstTensor AstMethodLet s (TKR (m' + n') r')
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
    AstConcrete{} ->  -- free variables possible, so can't compute the tensor
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstProjectR{} ->  -- TODO, but most likely reduced before it gets here
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstLetHVectorIn vars l v ->
      astLetHVectorIn vars l (astGatherCase sh4 v (vars4, ix4))
    Ast.AstRFromS{} {- @sh v -} -> Ast.AstGather sh4 v4 (vars4, ix4)
      -- TODO: this is broken
      {-
      let (takeSh, dropSh) = splitAt (valueOf @p') (shapeT @sh)
      in withShapeP takeSh $ \(Proxy @p_take) ->
         withShapeP dropSh $ \(Proxy @p_drop) ->
         gcastWith (unsafeCoerce Refl :: sh :~: p_take ++ p_drop) $
         gcastWith (unsafeCoerce Refl :: p_take :~: Take p' sh) $
         gcastWith (unsafeCoerce Refl :: p_drop :~: Drop p' sh) $
         gcastWith (unsafeCoerce Refl :: X.Rank sh :~: p' + n') $
         astRFromS $ astGatherStepS @_ @p' @sh v
                     ( ShapedList.listToSized $ sizedToList vars4
                     , ShapedList.listToSized $ indexToList ix4 ) -}

    Ast.AstApply{} -> Ast.AstGather sh4 v4 (vars4, ix4)

gatherFromNF :: forall m p. (KnownNat m, KnownNat p)
             => AstVarList m -> AstIndex AstMethodLet (1 + p) -> Bool
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

isVar :: AstTensor AstMethodLet s y -> Bool
isVar Ast.AstVar{} = True
isVar (Ast.AstFromPrimal Ast.AstVar{}) = True
isVar (Ast.AstPrimalPart Ast.AstVar{}) = True
isVar (Ast.AstDualPart Ast.AstVar{}) = True
isVar _ = False

astGatherKnobsS
  :: forall sh2 p sh s r.
     ( GoodScalar r, KnownShS sh, KnownShS sh2, KnownNat p
     , KnownShS (Take p sh), KnownShS (Drop p sh)
     , KnownShS (sh2 ++ Drop p sh) )
  => SimplifyKnobs -> AstTensor AstMethodLet s (TKS sh r)
  -> (AstVarListS sh2, AstIxS AstMethodLet (Take p sh))
  -> AstTensor AstMethodLet s (TKS (sh2 ++ Drop p sh) r)
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
    AstIntOp PlusIntOp [AstIntVar var2, AstConcrete i2]
      | var2 == var ->
        Just $ astSliceLax i2 k v0
    AstIntOp PlusIntOp [AstConcrete i2, AstIntVar var2]
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
      v2 = AstConcrete $ OR.fromPrimal (k - kMax : tail sh) 0
      !_A = assert (i < len
                    `blame` "astSlice: offset not smaller than tensor length"
                    `swith` (i, len)) ()
  in if | i == 0 && k == len -> v
        | k <= kMax -> AstSlice i k v
        | i == 0 -> AstAppend v v2
        | otherwise -> AstAppend (AstSlice i kMax v) v2
-}


-- * The simplifying combinators, one for each AST constructor

astPair :: (TensorKind x, TensorKind y)
         => AstTensor AstMethodLet s x -> AstTensor AstMethodLet s y
         -> AstTensor AstMethodLet s (TKProduct x y)
-- TODO, but maybe not the best idea?:
-- astPair (Ast.AstConcrete v1) (Ast.AstConcrete v2) =
--   Ast.AstConcrete (v1, v2)
astPair (Ast.AstFromPrimal v1) (Ast.AstFromPrimal v2) =
  Ast.AstFromPrimal $ astPair v1 v2
astPair v1 v2 = Ast.AstPair v1 v2

-- Inlining works for this let constructor, because it has just one variable,
-- unlike astLetHVectorIn, etc., so we don't try to eliminate it.
astLet :: forall y z s s2. (AstSpan s, AstSpan s2, TensorKind y, TensorKind z)
       => AstVarName s y -> AstTensor AstMethodLet s y
       -> AstTensor AstMethodLet s2 z
       -> AstTensor AstMethodLet s2 z
astLet _var _u v@Ast.AstConcrete{} = v
astLet var u v | astIsSmall True u =
  substituteAst u var v
astLet var u (Ast.AstFromPrimal v0) = Ast.AstFromPrimal $ astLet var u v0
astLet var u v@(Ast.AstVar _ var2) =
  case sameAstSpan @s @s2 of
    Just Refl -> case geq var2 var of
      Just Refl -> u
      _ -> v
    _ -> v
astLet var u v@(Ast.AstPrimalPart (Ast.AstVar _ var2)) =  -- a common noop
  case sameAstSpan @s @FullSpan of
    Just Refl -> case geq var2 var of
      Just Refl -> astPrimalPart u
      _ -> v
    _ -> v
astLet var u v@(Ast.AstDualPart (Ast.AstVar _ var2)) =  -- a noop
  case sameAstSpan @s @FullSpan of
    Just Refl -> case geq var2 var of
      Just Refl -> astDualPart u
      _ -> v
    _ -> v
astLet var (Ast.AstPair u1 u2) v =
  astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
    substituteAst (Ast.AstPair ast1 ast2) var v
astLet var (Ast.AstFromPrimal (Ast.AstPair u1 u2)) v =
  astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
    substituteAst (Ast.AstFromPrimal (Ast.AstPair ast1 ast2)) var v
astLet var (Ast.AstLet varN uN (Ast.AstPair u1 u2)) v =
  astLet varN uN
  $ astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
      substituteAst ( Ast.AstPair ast1 ast2) var v
astLet var (Ast.AstLetHVectorIn varsN lN (Ast.AstPair u1 u2)) v =
  astLetHVectorIn varsN lN
  $ astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
      substituteAst (Ast.AstPair ast1 ast2) var v
astLet var (Ast.AstFromPrimal (Ast.AstLet varN uN (Ast.AstPair u1 u2))) v =
  astLet varN uN
  $ astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
      substituteAst (Ast.AstFromPrimal (Ast.AstPair ast1 ast2)) var v
astLet var (Ast.AstFromPrimal (Ast.AstLetHVectorIn
                               varsN lN (Ast.AstPair u1 u2))) v =
  astLetHVectorIn varsN lN
  $ astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
      substituteAst (Ast.AstFromPrimal (Ast.AstPair ast1 ast2)) var v
astLet var u@(Ast.AstMkHVector l3) v =
  let shs = shapeAstHVector u
      f !vars !asts =
        let v2 = substituteAst (Ast.AstMkHVector asts)
                               var v
        in foldr (mapRankedShaped astLet astLet)
                 v2 (zip vars (V.toList l3))
  in fun1DToAst shs f
astLet var u@(Ast.AstFromPrimal (Ast.AstMkHVector l3)) v =
  let shs = shapeAstHVector u
      f !vars !asts =
        let v2 = substituteAst (Ast.AstMkHVector asts)
                               var v
            clet varC uC vC = astLet varC (Ast.AstFromPrimal uC) vC
        in foldr (mapRankedShaped clet clet)
                 v2 (zip vars (V.toList l3))
  in fun1DToAst shs f
astLet var (Ast.AstLet varN uN u@(Ast.AstMkHVector l3)) v =
  let shs = shapeAstHVector u
      f !vars !asts =
        let v2 = substituteAst (Ast.AstMkHVector asts)
                               var v
        in foldr (mapRankedShaped astLet astLet)
                 v2 (zip vars (V.toList l3))
  in astLet varN uN $ fun1DToAst shs f
astLet var (Ast.AstLetHVectorIn varsN lN u@(Ast.AstMkHVector l3)) v =
  let shs = shapeAstHVector u
      f !vars !asts =
        let v2 = substituteAst (Ast.AstMkHVector asts)
                               var v
        in foldr (mapRankedShaped astLet astLet)
                 v2 (zip vars (V.toList l3))
  in astLetHVectorIn varsN lN $ fun1DToAst shs f
astLet var (Ast.AstFromPrimal (Ast.AstLet varN uN u@(Ast.AstMkHVector l3))) v =
  let shs = shapeAstHVector u
      f !vars !asts =
        let v2 = substituteAst (Ast.AstMkHVector asts)
                               var v
            clet varC uC vC = astLet varC (Ast.AstFromPrimal uC) vC
        in foldr (mapRankedShaped clet clet)
                 v2 (zip vars (V.toList l3))
  in astLet varN uN $ fun1DToAst shs f
astLet var (Ast.AstFromPrimal (Ast.AstLetHVectorIn
                               varsN lN u@(Ast.AstMkHVector l3))) v =
  let shs = shapeAstHVector u
      f !vars !asts =
        let v2 = substituteAst (Ast.AstMkHVector asts)
                               var v
            clet varC uC vC = astLet varC (Ast.AstFromPrimal uC) vC
        in foldr (mapRankedShaped clet clet)
                 v2 (zip vars (V.toList l3))
  in astLetHVectorIn varsN lN $ fun1DToAst shs f
astLet var u v = Ast.AstLet var u v

-- A special variant to bind integer expressions inside indexes.
-- It check if the bound variables appears in the body at all.
-- Normally, that's asymptotically worse than doing this
-- in a global inlining pass, but we assume indexes expressions
-- are short and we need them simple ASAP.
astLetInt :: IntVarName -> AstInt AstMethodLet -> AstInt AstMethodLet -> AstInt AstMethodLet
astLetInt var u v | var `varNameInAst` v = astLet var u v
astLetInt _ _ v = v

astCond :: TensorKind y
        => AstBool ms -> AstTensor ms s y -> AstTensor ms s y -> AstTensor ms s y
astCond (AstBoolConst b) v w = if b then v else w
astCond b (Ast.AstFromPrimal v) (Ast.AstFromPrimal w) =
  Ast.AstFromPrimal $ astCond b v w
astCond b v w = Ast.AstCond b v w

astSumOfList :: (KnownNat n, GoodScalar r)
             => [AstTensor AstMethodLet s (TKR n r)] -> AstTensor AstMethodLet s (TKR n r)
astSumOfList = foldr1 (+)  -- @sum@ breaks and also reverse order

astSumOfListS :: (GoodScalar r, KnownShS sh, AstSpan s)
              => [AstTensor AstMethodLet s (TKS sh r)] -> AstTensor AstMethodLet s (TKS sh r)
astSumOfListS = foldr1 (+)  -- @sum@ reverses order

astSum :: (KnownNat n, GoodScalar r, AstSpan s)
       => AstTensor AstMethodLet s (TKR (1 + n) r) -> AstTensor AstMethodLet s (TKR n r)
astSum t0 = case shapeAst t0 of
  0 :$: rest -> astReplicate0N rest 0
--  1 :$: rest -> astReshape rest t0  -- TODO: slows down the CNNO test
  _ -> case t0 of
    -- Ast.AstLet var u v -> astLet var u (astSum v)
    -- this is problematic, because it keeps huge tensors alive for longer
    Ast.AstReplicate @y2 k v -> case stensorKind @y2 of
      STKR{} -> v * astReplicate0N (shapeAst v) (fromInteger $ fromSNat k)
      _ -> error "astSum: type family BuildTensorKind stuck at TKScalar"
    Ast.AstScatter (_ :$: sh) v (vars, _ :.: ix) -> astScatter sh v (vars, ix)
    Ast.AstFromVector l -> astSumOfList $ V.toList l
    Ast.AstSlice _i 0 v -> astReplicate0N (tailShape $ shapeAst v) 0
    Ast.AstSlice i 1 v -> astIndexR v (fromIntegral i :.: ZIR)
    Ast.AstReverse v -> astSum v
    AstConcrete (FTKR sh FTKScalar) t ->
      AstConcrete (FTKR (Nested.Internal.Shape.shrTail sh) FTKScalar) $ RepN $ tsumR $ unRepN t
    Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astSum v
    _ -> Ast.AstSum t0

astSumS :: forall n sh r s. (KnownNat n, KnownShS sh, GoodScalar r, AstSpan s)
        => AstTensor AstMethodLet s (TKS (n ': sh) r) -> AstTensor AstMethodLet s (TKS sh r)
astSumS t0 = case sameNat (Proxy @n) (Proxy @0) of
 Just Refl -> astReplicate0NS 0
 _ -> case sameNat (Proxy @n) (Proxy @1) of
  Just Refl -> astReshapeS t0
  _ -> case t0 of
    -- Ast.AstLet var u v -> astLet var u (astSumS v)
    Ast.AstReplicate @y2 k v -> case stensorKind @y2 of
      STKS{} -> v * astReplicate0NS (fromInteger $ fromSNat k)
      _ -> error "astSumS: type family BuildTensorKind stuck at TKScalar"
    Ast.AstScatterS @sh2 @p v (vars, _ :.$ ix) | Dict <- sixKnown ix ->
      case cmpNat (Proxy @1) (Proxy @p) of
        LTI ->
          gcastWith (unsafeCoerce Refl
                     :: Drop p (n : sh) :~: Drop (p - 1) sh) $
          gcastWith (unsafeCoerce Refl
                     :: Drop 1 (Take p (n : sh)) :~: Take (p - 1) sh) $
          astScatterS @sh2 @(p - 1) @sh v (vars, ix)
        EQI ->
          gcastWith (unsafeCoerce Refl
                     :: Drop p (n : sh) :~: Drop (p - 1) sh) $
          gcastWith (unsafeCoerce Refl
                     :: Drop 1 (Take p (n : sh)) :~: Take (p - 1) sh) $
          astScatterS @sh2 @(p - 1) @sh v (vars, ix)
        GTI -> error "astSumS: impossible p"
    Ast.AstFromVectorS l -> astSumOfListS $ V.toList l
    Ast.AstSliceS @_ @k _v | Just Refl <- sameNat (Proxy @k) (Proxy @0) -> astReplicate0NS 0
    Ast.AstSliceS @i @k v | Just Refl <- sameNat (Proxy @k) (Proxy @1) ->
      astIndexS v (valueOf @i :.$ ZIS)
    Ast.AstReverseS v -> astSumS v
    AstConcrete _ t -> AstConcrete (FTKS knownShS FTKScalar) $ RepN $ Nested.ssumOuter1 $ unRepN t
    Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astSumS v
    _ -> Ast.AstSumS t0

-- TODO: fuse scatters, scatter and sum, perhaps more (fromList?)
astScatter :: forall m n p s r.
              (GoodScalar r, KnownNat m, KnownNat n, KnownNat p, AstSpan s)
           => IShR (p + n) -> AstTensor AstMethodLet s (TKR (m + n) r)
           -> (AstVarList m, AstIndex AstMethodLet p)
           -> AstTensor AstMethodLet s (TKR (p + n) r)
astScatter _sh v (ZR, ZIR) = v
astScatter sh@(k :$: _) _v (_vars, AstConcrete _ it :.: _ix)
  | let i = fromIntegral $ Nested.sunScalar $ unRepN it
  , not (0 <= i && i < k) =
      astReplicate0N sh 0
-- else update (rzero sh 0) [AstConcreteS it] (astScatter ...)
astScatter sh v (var ::: vars, ix) | not $ varNameToAstVarId var `varInIndex` ix =
  astScatter sh (astSum v) (vars, ix)
-- astScatter sh v (ZR, ix) = update (rzero sh 0) ix v
astScatter sh (Ast.AstFromPrimal v) (vars, ix) =
  Ast.AstFromPrimal $ astScatter sh v (vars, ix)
astScatter sh v (vars, ix) = Ast.AstScatter sh v (vars, ix)

astScatterS :: forall sh2 p sh s r.
               ( KnownShS sh2, KnownShS sh, KnownNat p
               , KnownShS (Take p sh), KnownShS (Drop p sh)
               , KnownShS (sh2 ++ Drop p sh), GoodScalar r, AstSpan s )
            => AstTensor AstMethodLet s (TKS (sh2 ++ Drop p sh) r)
            -> (AstVarListS sh2, AstIxS AstMethodLet (Take p sh))
            -> AstTensor AstMethodLet s (TKS sh r)
astScatterS v (ZS, ZIS) =
  gcastWith (unsafeCoerce Refl
             :: Take p sh ++ Drop p sh :~: sh)
  v
astScatterS v (Const var ::$ (vars :: AstVarListS sh3), ix)
  | not $ varNameToAstVarId var `varInIndexS` ix
  , Dict <- slistKnown vars =
    withShapeP (shapeT @sh3
                ++ (shapeT @(Drop p sh))) $ \(Proxy @sh4) ->
      gcastWith (unsafeCoerce Refl :: sh3 ++ Drop p sh :~: sh4) $
      astScatterS @sh3 @p @sh (astSumS v) (vars, ix)
-- astScatterS v (ZR, ix) = update (rzero sh 0) ix v
astScatterS (Ast.AstFromPrimal v) (vars, ix) =
  Ast.AstFromPrimal $ astScatterS v (vars, ix)
astScatterS v (vars, ix) = Ast.AstScatterS v (vars, ix)

astFromVector :: forall s r n. (KnownNat n, GoodScalar r, AstSpan s)
              => Data.Vector.Vector (AstTensor AstMethodLet s (TKR n r))
              -> AstTensor AstMethodLet s (TKR (1 + n) r)
astFromVector v | V.length v == 1 = astReplicate (SNat @1) (v V.! 0)
astFromVector l | Just Refl <- sameAstSpan @s @PrimalSpan =
  let unConst :: AstTensor AstMethodLet PrimalSpan (TKR n r) -> Maybe (Nested.Ranked n r)
      unConst (AstConcrete _ (RepN t)) = Just t
      unConst _ = Nothing
  in case V.mapM unConst l of
    Just  l3 | V.length l3 >= 1 ->
      AstConcrete (FTKR (V.length l :$: Nested.rshape (l3 V.! 0)) FTKScalar) $ RepN $ tfromVectorR l3
    _ -> Ast.AstFromVector l
astFromVector l | Just Refl <- sameAstSpan @s @FullSpan =
  let unFromPrimal :: AstTensor AstMethodLet FullSpan (TKR n r) -> Maybe (AstTensor AstMethodLet PrimalSpan (TKR n r))
      unFromPrimal (Ast.AstFromPrimal t) = Just t
      unFromPrimal _ = Nothing
  in case V.mapM unFromPrimal l of
    Just l2 | V.null l2 -> Ast.AstFromVector V.empty
    Just l2 -> Ast.AstFromPrimal $ astFromVector l2
    Nothing -> Ast.AstFromVector l
astFromVector l = Ast.AstFromVector l

astFromVectorS :: forall s r n sh.
                  (KnownNat n, KnownShS sh, GoodScalar r, AstSpan s)
               => Data.Vector.Vector (AstTensor AstMethodLet s (TKS sh r))
               -> AstTensor AstMethodLet s (TKS (n ': sh) r)
astFromVectorS v | V.length v == 1 = astReplicate SNat (v V.! 0)
astFromVectorS l | Just Refl <- sameAstSpan @s @PrimalSpan =
  let unConst :: AstTensor AstMethodLet PrimalSpan (TKS sh r) -> Maybe (Nested.Shaped sh r)
      unConst (AstConcrete _ (RepN t)) = Just t
      unConst _ = Nothing
  in case V.mapM unConst l of
    Just l3 -> AstConcrete (FTKS knownShS FTKScalar) $ RepN $ tfromVectorS l3
    Nothing -> Ast.AstFromVectorS l
astFromVectorS l | Just Refl <- sameAstSpan @s @FullSpan =
  let unFromPrimal :: AstTensor AstMethodLet FullSpan (TKS sh r)
                 -> Maybe (AstTensor AstMethodLet PrimalSpan (TKS sh r))
      unFromPrimal (Ast.AstFromPrimal t) = Just t
      unFromPrimal _ = Nothing
  in case V.mapM unFromPrimal l of
    Just l2 | V.null l2 -> Ast.AstFromVectorS V.empty
    Just l2 -> Ast.AstFromPrimal $ astFromVectorS l2
    Nothing -> Ast.AstFromVectorS l
astFromVectorS l = Ast.AstFromVectorS l

astFromVectorX :: forall s r n sh.
                  (KnownNat n, KnownShX sh, GoodScalar r, AstSpan s)
               => Data.Vector.Vector (AstTensor AstMethodLet s (TKX sh r))
               -> AstTensor AstMethodLet s (TKX (Just n ': sh) r)
astFromVectorX v | V.length v == 1 = astReplicate SNat (v V.! 0)
astFromVectorX l | Just Refl <- sameAstSpan @s @PrimalSpan =
  let unConst :: AstTensor AstMethodLet PrimalSpan (TKX sh r) -> Maybe (Nested.Mixed sh r)
      unConst (AstConcrete _ (RepN t)) = Just t
      unConst _ = Nothing
  in case V.mapM unConst l of
    Just l3 | V.length l3 >= 1 ->
      AstConcrete (FTKX (SKnown (SNat @n) :$% Nested.mshape (l3 V.! 0)) FTKScalar) $ RepN $ tfromVectorX l3
    _ -> Ast.AstFromVectorX l
astFromVectorX l | Just Refl <- sameAstSpan @s @FullSpan =
  let unFromPrimal :: AstTensor AstMethodLet FullSpan (TKX sh r)
                 -> Maybe (AstTensor AstMethodLet PrimalSpan (TKX sh r))
      unFromPrimal (Ast.AstFromPrimal t) = Just t
      unFromPrimal _ = Nothing
  in case V.mapM unFromPrimal l of
    Just l2 | V.null l2 -> Ast.AstFromVectorX V.empty
    Just l2 -> Ast.AstFromPrimal $ astFromVectorX l2
    Nothing -> Ast.AstFromVectorX l
astFromVectorX l = Ast.AstFromVectorX l

astReplicate :: forall k y s. (TensorKind y, AstSpan s)
             => SNat k -> AstTensor AstMethodLet s y -> AstTensor AstMethodLet s (BuildTensorKind k y)
astReplicate snat@SNat
 | Dict <- lemTensorKindOfBuild snat (stensorKind @y) = \case
{- TODO: these may be counterproductive with many gathers and their fusion
         though these let transpose cancel out with each other sometimes
         (instead we should try to cancel out inside replicate and only move
          if they don't) -}
  Ast.AstTranspose perm v ->
    astTranspose (0 : map succ perm) $ astReplicate snat v
{- see the previous comment
  Ast.AstReshape sh v ->
    AstReshape (k :$: sh) $ astReplicate k v
-}
-- This allocates a big tensor too early, while it's still possible
-- a projection reduces this away. The cost to AD should not be too high.
-- This would also hide AstReplicate from hacks that recover tmatmul2, etc.
--  AstConcrete t -> AstConcrete $ treplicateR k t
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astReplicate snat v
  Ast.AstTransposeS @perm @sh1 perm v -> case stensorKind @y of
    STKS @sh _ _ ->
      let zsuccPerm :: Permutation.Perm (0 : Permutation.MapSucc perm)
          zsuccPerm = Permutation.permShift1 perm
      in
        gcastWith (unsafeCoerce Refl
                   :: Permutation.PermutePrefix (0 : Permutation.MapSucc perm) (k : sh1) :~: k : sh) $
        gcastWith (unsafeCoerce Refl :: Rank (0 : Permutation.MapSucc perm) :~: 1 + Rank perm) $
        trustMeThisIsAPermutation @(0 : Permutation.MapSucc perm) $
        astTransposeS zsuccPerm $ astReplicate snat v
  v -> Ast.AstReplicate snat v

astReplicateN :: forall n p s r.
                 (KnownNat n, KnownNat p, GoodScalar r, AstSpan s)
              => IShR (n + p) -> AstTensor AstMethodLet s (TKR p r)
              -> AstTensor AstMethodLet s (TKR (n + p) r)
astReplicateN sh v =
  let go :: IShR n' -> AstTensor AstMethodLet s (TKR (n' + p) r)
      go ZSR = v
      go (k :$: sh2) | Dict <- knownShR sh2 = withSNat k $ \snat ->
        astReplicate snat $ go sh2
  in go (takeShape sh)

astReplicateNS :: forall shn shp s r.
                  (KnownShS shn, KnownShS shp, GoodScalar r, AstSpan s)
               => AstTensor AstMethodLet s (TKS shp r) -> AstTensor AstMethodLet s (TKS (shn ++ shp) r)
astReplicateNS v =
  let go :: ShS shn' -> AstTensor AstMethodLet s (TKS (shn' ++ shp) r)
      go ZSS = v
      go ((:$$) @k @shn2 SNat shn2) | Dict <- sshapeKnown shn2 =
        withShapeP (shapeT @shn2 ++ shapeT @shp) $ \(Proxy @sh) ->
          gcastWith (unsafeCoerce Refl :: sh :~: shn2 ++ shp) $
          astReplicate (SNat @k) $ go shn2
  in go (knownShS @shn)

astReplicate0N :: forall n s r. (GoodScalar r, AstSpan s)
               => IShR n -> r -> AstTensor AstMethodLet s (TKR n r)
astReplicate0N sh = astReplicate0NT sh . fromPrimal . AstConcrete (FTKR ZSR FTKScalar) . RepN . Nested.rscalar

astReplicate0NS :: forall shn s r. (KnownShS shn, GoodScalar r, AstSpan s)
                => r -> AstTensor AstMethodLet s (TKS shn r)
astReplicate0NS =
  let go :: ShS sh' -> AstTensor AstMethodLet s (TKS '[] r) -> AstTensor AstMethodLet s (TKS sh' r)
      go ZSS v = v
      go ((:$$) SNat sh') v | Dict <- sshapeKnown sh' = astReplicate SNat $ go sh' v
  in go (knownShS @shn) . fromPrimal . AstConcrete (FTKS ZSS FTKScalar) . RepN . Nested.sscalar

astReplicate0NT :: forall n s r. (GoodScalar r, AstSpan s)
                => IShR n -> AstTensor AstMethodLet s (TKR 0 r) -> AstTensor AstMethodLet s (TKR n r)
astReplicate0NT sh =
  let go :: IShR n' -> AstTensor AstMethodLet s (TKR 0 r) -> AstTensor AstMethodLet s (TKR n' r)
      go ZSR v = v
      go (k :$: sh') v | Dict <- knownShR sh' = withSNat k $ \snat ->
        astReplicate snat $ go sh' v
  in go sh

astAppend :: (KnownNat n, GoodScalar r, AstSpan s)
          => AstTensor AstMethodLet s (TKR (1 + n) r) -> AstTensor AstMethodLet s (TKR (1 + n) r)
          -> AstTensor AstMethodLet s (TKR (1 + n) r)
astAppend (AstConcrete (FTKR (ulen :$: sh) FTKScalar) u)
          (AstConcrete (FTKR (vlen :$: _) FTKScalar) v) =
  AstConcrete (FTKR (ulen + vlen :$: sh) FTKScalar) $ RepN $ tappendR (unRepN u) (unRepN v)
astAppend (Ast.AstFromPrimal u) (Ast.AstFromPrimal v) =
  Ast.AstFromPrimal $ astAppend u v
astAppend (Ast.AstFromVector l1) (Ast.AstFromVector l2) =
  astFromVector $ l1 V.++ l2
astAppend u v = Ast.AstAppend u v

astAppendS :: (KnownNat m, KnownNat n, KnownShS sh, GoodScalar r, AstSpan s)
           => AstTensor AstMethodLet s (TKS (m ': sh) r) -> AstTensor AstMethodLet s (TKS (n ': sh) r)
           -> AstTensor AstMethodLet s (TKS ((m + n) ': sh) r)
astAppendS (AstConcrete _ u) (AstConcrete _ v) =
  AstConcrete (FTKS knownShS FTKScalar) $ RepN $ tappendS (unRepN u) (unRepN v)
astAppendS (Ast.AstFromPrimal u) (Ast.AstFromPrimal v) =
  Ast.AstFromPrimal $ astAppendS u v
astAppendS (Ast.AstFromVectorS l1) (Ast.AstFromVectorS l2) =
  astFromVectorS $ l1 V.++ l2
astAppendS u v = Ast.AstAppendS u v

astSlice :: forall k s r. (KnownNat k, GoodScalar r, AstSpan s)
         => Int -> Int -> AstTensor AstMethodLet s (TKR (1 + k) r)
         -> AstTensor AstMethodLet s (TKR (1 + k) r)
astSlice i n (AstConcrete (FTKR (_ :$: sh) FTKScalar) t) =
  AstConcrete (FTKR (n :$: sh) FTKScalar) $ RepN $ tsliceR i n (unRepN t)
astSlice i n (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astSlice i n v
astSlice 0 n v | n == lengthAst v = v
astSlice _i n (Ast.AstReplicate @y2 _ v) = case stensorKind @y2 of
  STKR{} -> withSNat n $ \snat -> astReplicate snat v
  _ -> error "astSlice: type family BuildTensorKind stuck at TKScalar"
astSlice i n (Ast.AstFromVector l) = astFromVector $ V.take n (V.drop i l)
astSlice i n w@(Ast.AstAppend (u :: AstTensor AstMethodLet s (TKR (1 + k) r))
                              (v :: AstTensor AstMethodLet s (TKR (1 + k) r))) =
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
              ivar var ix
  in astGatherR (n :$: sh') v (var ::: vars, ix2)
astSlice i n v = Ast.AstSlice i n v

astSliceS :: forall i n k sh s r.
             ( KnownNat i, KnownNat n, KnownNat k, KnownShS sh, GoodScalar r
             , AstSpan s )
          => AstTensor AstMethodLet s (TKS (i + n + k ': sh) r)
          -> AstTensor AstMethodLet s (TKS (n ': sh) r)
astSliceS (AstConcrete _ t) =
  AstConcrete (FTKS knownShS FTKScalar) $ RepN $ tsliceS @i @n (unRepN t)
astSliceS (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astSliceS @i @n v
astSliceS v | Just Refl <- sameNat (Proxy @i) (Proxy @0)
            , Just Refl <- sameNat (Proxy @k) (Proxy @0) = v
astSliceS (Ast.AstReplicate @y2 _ v) = case stensorKind @y2 of
  STKS{} -> astReplicate (SNat @n) v
  _ -> error "astSliceS: type family BuildTensorKind stuck at TKScalar"
astSliceS (Ast.AstFromVectorS l) =
  astFromVectorS $ V.take (valueOf @n) (V.drop (valueOf @i) l)
astSliceS w@(Ast.AstAppendS (u :: AstTensor AstMethodLet s (TKS (ulen : sh) r))
                            (v :: AstTensor AstMethodLet s (TKS (vlen : sh) r))) =
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
      ix2 = substituteAstIxS  -- cheap subst, because ivar is tiny
              ivar var ix
      vars2 = Const var ::$ vars
  in case slistKnown vars2 of
    Dict -> astGatherS @(n : sh21) @p @sh4 v (vars2, ix2)
astSliceS v = Ast.AstSliceS @i v

astReverse :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
           => AstTensor AstMethodLet s (TKR (1 + n) r) -> AstTensor AstMethodLet s (TKR (1 + n) r)
astReverse (AstConcrete ftk t) = AstConcrete ftk $ RepN $ treverseR (unRepN t)
astReverse (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astReverse v
astReverse (Ast.AstReplicate k v) = astReplicate k v
astReverse (Ast.AstFromVector l) = astFromVector $ V.reverse l
astReverse (Ast.AstReverse v) = v
astReverse (Ast.AstGather sh@(k :$: _) v (var ::: vars, ix)) =
  let ivar = fromIntegral k - AstIntVar var
      ix2 = substituteAstIndex  -- cheap subst, because ivar is tiny
              ivar var ix
  in astGatherR sh v (var ::: vars, ix2)
astReverse v = Ast.AstReverse v

astReverseS :: forall n sh s r. (KnownNat n, KnownShS sh, GoodScalar r, AstSpan s)
            => AstTensor AstMethodLet s (TKS (n ': sh) r) -> AstTensor AstMethodLet s (TKS (n ': sh) r)
astReverseS (AstConcrete ftk t) = AstConcrete ftk $ RepN $ treverseS (unRepN t)
astReverseS (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astReverseS v
astReverseS (Ast.AstReplicate k v) = astReplicate k v
astReverseS (Ast.AstFromVectorS l) = astFromVectorS $ V.reverse l
astReverseS (Ast.AstReverseS v) = v
astReverseS (Ast.AstGatherS v ((::$) @k (Const var) vars, ix)) =
  let ivar = valueOf @k - AstIntVar var
      ix2 = substituteAstIxS  -- cheap subst, because ivar is tiny
              ivar var ix
  in astGatherS v (Const var ::$ vars, ix2)
astReverseS v = Ast.AstReverseS v

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astTransposeAsGather needs to be called in addition
-- if full simplification is required.
astTranspose :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
             => Permutation.PermR -> AstTensor AstMethodLet s (TKR n r)
             -> AstTensor AstMethodLet s (TKR n r)
astTranspose perm = \case
  t | null perm -> t
  Ast.AstLet var u v -> astLet var u (astTranspose perm v)
  AstN1R opCode u | not (isVar u) -> AstN1R opCode (astTranspose perm u)
  AstN2R opCode u v | not (isVar u && isVar v) ->
    AstN2R opCode (astTranspose perm u) (astTranspose perm v)
  Ast.AstR1R opCode u | not (isVar u) -> Ast.AstR1R opCode (astTranspose perm u)
  Ast.AstR2R opCode u v | not (isVar u && isVar v) ->
    Ast.AstR2R opCode (astTranspose perm u) (astTranspose perm v)
  Ast.AstSum v -> astSum $ astTranspose (0 : map succ perm) v
  Ast.AstScatter @_ @_ @p sh v (vars, ix) | length perm <= valueOf @p ->
    -- TODO: should the below be backpermute or permute?
    astScatter (Nested.Internal.Shape.shrPermutePrefix perm sh) v
               (vars, Nested.Internal.Shape.ixrPermutePrefix perm ix)
  Ast.AstTranspose perm2 t ->
    let perm2Matched =
          perm2
          ++ take (length perm - length perm2) (drop (length perm2) [0 ..])
        perm3 = normalizePermutation $ backpermutePrefixList perm perm2Matched
    in astTranspose perm3 t
      -- this rule can be disabled to test fusion of gathers
  -- Note that the following would be wrong, because transpose really
  -- changes the linearisation order, while reshape only modifies indexing:
  -- (perm, AstReshape sh v) -> astReshape (Nested.Internal.Shape.shrPermutePrefix perm sh) v
  Ast.AstGather @m sh v (vars, ix) | length perm <= valueOf @m ->
    -- TODO: should the below be backpermute or permute?
    astGatherR (Nested.Internal.Shape.shrPermutePrefix perm sh) v
               (Nested.Internal.Shape.listrPermutePrefix perm vars, ix)
  AstConcrete (FTKR sh FTKScalar) t -> AstConcrete (FTKR (Nested.Internal.Shape.shrPermutePrefix perm sh) FTKScalar) $ RepN $ ttransposeR perm (unRepN t)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astTranspose perm v
  u -> Ast.AstTranspose perm u
    -- we don't go inside AstSumOfList, because they are usually long

astTransposeS :: forall perm sh s r.
                 ( PermC perm, KnownShS sh, Rank perm <= Rank sh
                 , GoodScalar r, AstSpan s )
              => Permutation.Perm perm -> AstTensor AstMethodLet s (TKS sh r)
              -> AstTensor AstMethodLet s (TKS (Permutation.PermutePrefix perm sh) r)
astTransposeS perm t = case perm of
 Permutation.PNil -> t
 _ -> case t of
  Ast.AstLet var u v ->
    withShapeP (backpermutePrefixList (Permutation.permToList' perm)
                                      (shapeT @sh)) $ \(Proxy @shp) ->
    gcastWith (unsafeCoerce Refl :: Permutation.PermutePrefix perm sh :~: shp) $
    astLet var u (astTransposeS perm v)
  AstN1S opCode u | not (isVar u) ->
    withShapeP (backpermutePrefixList (Permutation.permToList' perm)
                                      (shapeT @sh)) $ \(Proxy @shp) ->
    gcastWith (unsafeCoerce Refl :: Permutation.PermutePrefix perm sh :~: shp) $
    AstN1S opCode (astTransposeS perm u)
  AstN2S opCode u v | not (isVar u && isVar v) ->
    withShapeP (backpermutePrefixList (Permutation.permToList' perm)
                                      (shapeT @sh)) $ \(Proxy @shp) ->
    gcastWith (unsafeCoerce Refl :: Permutation.PermutePrefix perm sh :~: shp) $
    AstN2S opCode (astTransposeS perm u) (astTransposeS perm v)
  Ast.AstR1S opCode u | not (isVar u) ->
    withShapeP (backpermutePrefixList (Permutation.permToList' perm)
                                      (shapeT @sh)) $ \(Proxy @shp) ->
    gcastWith (unsafeCoerce Refl :: Permutation.PermutePrefix perm sh :~: shp) $
   Ast.AstR1S opCode (astTransposeS perm u)
  Ast.AstR2S opCode u v | not (isVar u && isVar v) ->
    withShapeP (backpermutePrefixList (Permutation.permToList' perm)
                                      (shapeT @sh)) $ \(Proxy @shp) ->
    gcastWith (unsafeCoerce Refl :: Permutation.PermutePrefix perm sh :~: shp) $
   Ast.AstR2S opCode (astTransposeS perm u) (astTransposeS perm v)
  Ast.AstSumS @n v ->
    let zsuccP :: Permutation.Perm (0 : Permutation.MapSucc perm)
        zsuccP = Permutation.permShift1 perm
    in
      withShapeP (backpermutePrefixList (Permutation.permToList' perm)
                                        (shapeT @sh)) $ \(Proxy @shp) ->
        gcastWith (unsafeCoerce Refl :: Permutation.PermutePrefix perm sh :~: shp) $
        gcastWith (unsafeCoerce Refl :: Rank (0 : Permutation.MapSucc perm)
                                        :~: 1 + Rank perm) $
        gcastWith (unsafeCoerce Refl
                   :: Permutation.PermutePrefix (0 : Permutation.MapSucc perm) (n : sh)
                      :~: n : Permutation.PermutePrefix perm sh) $
        trustMeThisIsAPermutation @(0 : Permutation.MapSucc perm) $
        astSumS $ astTransposeS zsuccP v
  Ast.AstScatterS @sh2 @p v (vars, ix)
    -- TODO: should the below be backpermute or permute?
    | length (Permutation.permToList' perm) <= length (shapeT @(Take p sh)) ->
      withShapeP
        (backpermutePrefixList (Permutation.permToList' perm)
                               (shapeT @sh)) $ \(Proxy @shPerm) ->
          gcastWith (X.unsafeCoerceRefl :: Permutation.PermutePrefix perm sh :~: shPerm) $
        withShapeP (take (length ix)
                       $ shapeT @shPerm) $ \(Proxy @shpPerm) ->
          gcastWith (X.unsafeCoerceRefl :: Take p shPerm :~: shpPerm) $
          gcastWith (X.unsafeCoerceRefl
                     :: Permutation.PermutePrefix perm (Take p sh)
                        :~: shpPerm) $
          let ix2 :: AstIxS AstMethodLet (Take p shPerm) =
                Nested.Internal.Shape.ixsPermutePrefix perm ix
          in gcastWith (X.unsafeCoerceRefl
                        :: Drop p shPerm :~: Drop p sh) $
             astScatterS @sh2 @p @shPerm v (vars, ix2)
{- TODO: failed higher level approach:
      case ShapedList.ixsLengthSNat ix of
        (SNat :: SNat p') ->
          gcastWith (X.unsafeCoerceRefl :: p' :~: p) $
          let sh :: Nested.ShS sh
              sh = knownShS @sh
              shPerm :: Nested.ShS (Permutation.PermutePrefix perm sh)
              shPerm = Nested.Internal.Shape.applyPermShS perm sh
              shpPerm :: Nested.ShS (Take p (Permutation.PermutePrefix perm sh))
              shpPerm = ShapedList.takeShS @p shPerm
          in
              gcastWith (unsafeCoerce Refl
                         :: Permutation.PermutePrefix perm (Take p sh)
                            :~: (Take p (Permutation.PermutePrefix perm sh))) $
              let ix2 :: AstIxS (Take p (Permutation.PermutePrefix perm sh)) =
                    Nested.Internal.Shape.ixsPermutePrefix perm ix
              in gcastWith (unsafeCoerce Refl
                            :: Drop p (Permutation.PermutePrefix perm sh) :~: Drop p sh) $
                 astScatterS @sh2 @p @(Permutation.PermutePrefix perm sh) v (vars, ix2)
-}
  Ast.AstTransposeS @_ @sh2 perm2 u ->  -- TODO: try to perform at type level
    let permV = Permutation.permToList' perm
        perm2V = Permutation.permToList' perm2
        perm2Matched =
          perm2V
          ++ take (length permV - length perm2V) (drop (length perm2V) [0 ..])
        perm3V = normalizePermutation $ backpermutePrefixList permV perm2Matched
    in Permutation.permFromList perm3V $ \(perm3 :: Permutation.Perm perm3) ->
      trustMeThisIsAPermutation @perm3 $
      gcastWith (unsafeCoerce Refl
                 :: Permutation.PermutePrefix perm3 sh2
                    :~: Permutation.PermutePrefix perm sh) $
      case compare (length perm3V)
                   (Nested.Internal.Shape.shsLength (knownShS @sh2)) of
        LT -> gcastWith (unsafeCoerce Refl
                         :: Compare (Rank perm3) (Rank sh2) :~: LT) $
              astTransposeS perm3 u
        EQ -> gcastWith (unsafeCoerce Refl
                         :: Compare (Rank perm3) (Rank sh2) :~: EQ) $
              astTransposeS perm3 u
        GT -> error "astTransposeS: GT"
  Ast.AstGatherS @sh2 @p @sh3 v (vars, ix)
    -- TODO: should the below be backpermute or permute?
    | length (Permutation.permToList' perm) <= length (shapeT @sh2) ->
      withShapeP (backpermutePrefixList (Permutation.permToList' perm)
                                      (shapeT @sh)) $ \(Proxy @shp) ->
      gcastWith (unsafeCoerce Refl :: Permutation.PermutePrefix perm sh :~: shp) $
      withShapeP (backpermutePrefixList
                    (Permutation.permToList' perm)
                    (shapeT @sh2)) $ \(Proxy @shmPerm) ->
        gcastWith (unsafeCoerce Refl
                   :: Permutation.PermutePrefix perm sh2 :~: shmPerm) $
        let vars2 :: AstVarListS shmPerm =
              Nested.Internal.Shape.listsPermutePrefix perm vars
        in gcastWith (unsafeCoerce Refl
                      :: Permutation.PermutePrefix perm sh2 ++ Drop p sh3
                         :~: Permutation.PermutePrefix perm sh) $
           astGatherS @shmPerm @p @sh3 v (vars2, ix)
 -- TODO: AstConcreteS t -> AstConcreteS $ ttransposeS @perm t
  Ast.AstFromPrimal v ->
    withShapeP (backpermutePrefixList (Permutation.permToList' perm)
                                      (shapeT @sh)) $ \(Proxy @shp) ->
    gcastWith (unsafeCoerce Refl :: Permutation.PermutePrefix perm sh :~: shp) $
    Ast.AstFromPrimal $ astTransposeS perm v
  u -> Ast.AstTransposeS @perm perm u  -- TODO

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astReshapeAsGather needs to be called in addition
-- if full simplification is required.
astReshape :: forall p m s r. (KnownNat p, KnownNat m, GoodScalar r, AstSpan s)
           => IShR m -> AstTensor AstMethodLet s (TKR p r) -> AstTensor AstMethodLet s (TKR m r)
astReshape shOut = \case
  Ast.AstReplicate @y2 (SNat @k) x
    | Just Refl <- sameNat (Proxy @k) (Proxy @1) ->
      case stensorKind @y2 of
        STKR{} -> astReshape shOut x
        _ -> error "astReshape: type family BuildTensorKind stuck at TKScalar"
  Ast.AstLet var u v -> astLet var u (astReshape shOut v)
  AstN1R opCode u | not (isVar u) -> AstN1R opCode (astReshape shOut u)
  AstN2R opCode u v | not (isVar u && isVar v) ->
    AstN2R opCode (astReshape shOut u) (astReshape shOut v)
  Ast.AstR1R opCode u | not (isVar u) -> Ast.AstR1R opCode (astReshape shOut u)
  Ast.AstR2R opCode u v | not (isVar u && isVar v) ->
    Ast.AstR2R opCode (astReshape shOut u) (astReshape shOut v)
  Ast.AstFromVector l | [x] <- V.toList l -> astReshape shOut x
  Ast.AstReshape _ v -> astReshape shOut v
  AstConcrete _ t -> AstConcrete (FTKR shOut FTKScalar) $ RepN $ Nested.rreshape shOut (unRepN t)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astReshape shOut v
  v -> let shIn = shapeAst v
       in case sameNat (Proxy @p) (Proxy @m) of
         Just Refl -> if shIn == shOut
                      then v
                      else Ast.AstReshape shOut v
         _ -> Ast.AstReshape shOut v

astReshapeS :: forall sh sh2 r s.
               ( KnownShS sh, KnownShS sh2, Nested.Product sh ~ Nested.Product sh2
               , GoodScalar r, AstSpan s )
            => AstTensor AstMethodLet s (TKS sh r) -> AstTensor AstMethodLet s (TKS sh2 r)
astReshapeS = \case
  Ast.AstReplicate @y2 (SNat @k) x
    | Just Refl <- sameNat (Proxy @k) (Proxy @1) ->
      case stensorKind @y2 of
        STKS sh _ -> withKnownShS sh $ astReshapeS x
        _ -> error "astReshapeS: type family BuildTensorKind stuck at TKScalar"
  Ast.AstLet var u v -> astLet var u (astReshapeS @_ @sh2 v)
  AstN1S opCode u | not (isVar u) -> AstN1S opCode (astReshapeS @_ @sh2 u)
  AstN2S opCode u v | not (isVar u && isVar v) ->
    AstN2S opCode (astReshapeS @_ @sh2 u) (astReshapeS @_ @sh2 v)
  Ast.AstR1S opCode u | not (isVar u) ->
    Ast.AstR1S opCode (astReshapeS @_ @sh2 u)
  Ast.AstR2S opCode u v | not (isVar u && isVar v) ->
    Ast.AstR2S opCode (astReshapeS @_ @sh2 u) (astReshapeS @_ @sh2 v)
  Ast.AstFromVectorS @n l | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
    astReshapeS $ l V.! 0
  Ast.AstReshapeS v -> astReshapeS @_ @sh2 v
  AstConcrete _ t -> AstConcrete (FTKS knownShS FTKScalar) $ RepN $ treshapeS (unRepN t)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astReshapeS v
  v -> case sameShape @sh @sh2 of
         Just Refl -> v
         _ -> Ast.AstReshapeS v

astCast :: (KnownNat n, GoodScalar r1, GoodScalar r2, RealFrac r1, RealFrac r2)
        => AstTensor AstMethodLet s (TKR n r1) -> AstTensor AstMethodLet s (TKR n r2)
astCast (AstConcrete (FTKR sh FTKScalar) t) = AstConcrete (FTKR sh FTKScalar) $ RepN $ tcastR (unRepN t)
astCast (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astCast v
astCast (Ast.AstCast v) = astCast v
astCast (Ast.AstFromIntegral v) = astFromIntegral v
astCast v = Ast.AstCast v

astCastS :: ( KnownShS sh, GoodScalar r1, GoodScalar r2, RealFrac r1
            , RealFrac r2 )
         => AstTensor AstMethodLet s (TKS sh r1) -> AstTensor AstMethodLet s (TKS sh r2)
astCastS (AstConcrete (FTKS sh FTKScalar) t) = AstConcrete (FTKS sh FTKScalar) $ RepN $ tcastS (unRepN t)
astCastS (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astCastS v
astCastS (Ast.AstCastS v) = astCastS v
astCastS (Ast.AstFromIntegralS v) = astFromIntegralS v
astCastS v = Ast.AstCastS v

astFromIntegral :: (KnownNat n, GoodScalar r1, GoodScalar r2, Integral r1)
                => AstTensor AstMethodLet PrimalSpan (TKR n r1)
                -> AstTensor AstMethodLet PrimalSpan (TKR n r2)
astFromIntegral (AstConcrete (FTKR sh FTKScalar) t) = AstConcrete (FTKR sh FTKScalar) $ RepN $ tfromIntegralR (unRepN t)
astFromIntegral (Ast.AstFromIntegral v) = astFromIntegral v
astFromIntegral v = Ast.AstFromIntegral v

astFromIntegralS :: (KnownShS sh, GoodScalar r1, GoodScalar r2, Integral r1)
                 => AstTensor AstMethodLet PrimalSpan (TKS sh r1)
                 -> AstTensor AstMethodLet PrimalSpan (TKS sh r2)
astFromIntegralS (AstConcrete (FTKS sh FTKScalar) t) = AstConcrete (FTKS sh FTKScalar) $ RepN $ tfromIntegralS (unRepN t)
astFromIntegralS (Ast.AstFromIntegralS v) = astFromIntegralS v
astFromIntegralS v = Ast.AstFromIntegralS v

astProject1
  :: forall x z s. (TensorKind x, TensorKind z, AstSpan s)
  => AstTensor AstMethodLet s (TKProduct x z) -> AstTensor AstMethodLet s x
astProject1 u = case u of
  Ast.AstPair x _z -> x
  Ast.AstLet var t v -> Ast.AstLet var t (astProject1 v)
  Ast.AstLetHVectorIn vars l v -> astLetHVectorIn vars l (astProject1 v)
-- TODO: generalize AstConcrete, unless it's not the best idea? currently these must be explicit AstPair, so the other rule works fine:  Ast.AstConcrete u1 -> Ast.AstConcrete $ tproject1 u1
  Ast.AstFromPrimal u1 -> Ast.AstFromPrimal $ astProject1 u1
  Ast.AstCond b v1 v2 -> Ast.AstCond b (astProject1 v1) (astProject1 v2)
  _ -> Ast.AstProject1 u

astProject2
  :: forall x z s. (TensorKind x, TensorKind z, AstSpan s)
  => AstTensor AstMethodLet s (TKProduct x z) -> AstTensor AstMethodLet s z
astProject2 u = case u of
  Ast.AstPair _x z -> z
  Ast.AstLet var t v -> Ast.AstLet var t (astProject2 v)
  Ast.AstLetHVectorIn vars l v -> astLetHVectorIn vars l (astProject2 v)
  Ast.AstFromPrimal u1 -> Ast.AstFromPrimal $ astProject2 u1
  Ast.AstCond b v1 v2 -> Ast.AstCond b (astProject2 v1) (astProject2 v2)
  _ -> Ast.AstProject2 u

astProjectR
  :: forall n r s. (KnownNat n, GoodScalar r, AstSpan s)
  => AstTensor AstMethodLet s TKUntyped -> Int
  -> AstTensor AstMethodLet s (TKR n r)
astProjectR l p = case l of
  Ast.AstMkHVector l3 ->
    fromDynamicR (\sh -> astReplicate0N sh 0) (l3 V.! p)
  Ast.AstLet var u2 d2 ->
    astLet var u2 (astProjectR d2 p)
  Ast.AstLetHVectorIn vars d1 d2 ->
    astLetHVectorIn vars d1 (astProjectR d2 p)
  Ast.AstFromPrimal l1 -> Ast.AstFromPrimal $ astProjectR l1 p
  Ast.AstCond b v1 v2 -> Ast.AstCond b (astProjectR v1 p) (astProjectR v2 p)
  _ -> Ast.AstProjectR l p

astProjectS
  :: forall sh r s. (KnownShS sh, GoodScalar r, AstSpan s)
  => AstTensor AstMethodLet s TKUntyped -> Int
  -> AstTensor AstMethodLet s (TKS sh r)
astProjectS l p = case l of
  Ast.AstMkHVector l3 ->
    fromDynamicS (astReplicate0NS 0) (l3 V.! p)
  Ast.AstLet var u2 d2 ->
    astLet var u2 (astProjectS d2 p)
  Ast.AstLetHVectorIn vars d1 d2 ->
    astLetHVectorIn vars d1 (astProjectS d2 p)
  Ast.AstFromPrimal l1 -> Ast.AstFromPrimal $ astProjectS l1 p
  Ast.AstCond b v1 v2 -> Ast.AstCond b (astProjectS v1 p) (astProjectS v2 p)
  _ -> Ast.AstProjectS l p

astNestS
  :: forall r sh1 sh2 ms s.
     (GoodScalar r, KnownShS sh1, KnownShS sh2, KnownShS (sh1 ++ sh2), AstSpan s)
  => AstTensor ms s (TKS (sh1 ++ sh2) r)
  -> AstTensor ms s (TKS2 sh1 (TKS sh2 r))
astNestS t = case t of
  Ast.AstLet var u2 d2 ->  -- TODO: good idea?
    astLet var u2 (astNestS d2)
  Ast.AstFromPrimal u -> Ast.AstFromPrimal $ astNestS u
  Ast.AstCond b v1 v2 -> Ast.AstCond b (astNestS v1) (astNestS v2)  -- TODO: ??
-- TODO: when sh agrees:  Ast.AstUnNestS u -> u
  _ -> Ast.AstNestS t

astUnNestS
  :: forall r sh1 sh2 ms s.
     (GoodScalar r, KnownShS sh1, KnownShS sh2, KnownShS (sh1 ++ sh2), AstSpan s)
  => AstTensor ms s (TKS2 sh1 (TKS sh2 r))
  -> AstTensor ms s (TKS (sh1 ++ sh2) r)
astUnNestS t = case t of
  Ast.AstLet var u2 d2 ->  -- TODO: good idea?
    astLet var u2 (astUnNestS d2)
  Ast.AstFromPrimal u -> Ast.AstFromPrimal $ astUnNestS u
  Ast.AstCond b v1 v2 -> Ast.AstCond b (astUnNestS v1) (astUnNestS v2)  -- TODO: ??
  Ast.AstNestS u -> u
  _ -> Ast.AstUnNestS t

astRFromS :: forall sh s r. (GoodScalar r, KnownShS sh)
          => AstTensor AstMethodLet s (TKS sh r) -> AstTensor AstMethodLet s (TKR (Rank sh) r)
astRFromS (AstConcrete _ t) =
  withListSh (Proxy @sh) $ \(_ :: IShR p) ->
  gcastWith (unsafeCoerce Refl :: Rank sh :~: p) $
  let u = Nested.stoRanked (unRepN t)
  in AstConcrete (FTKR (Nested.rshape u) FTKScalar) (RepN u)
astRFromS (Ast.AstFromPrimal v) =
  withListSh (Proxy @sh) $ \(_ :: IShR p) ->
  gcastWith (unsafeCoerce Refl :: Rank sh :~: p) $
  Ast.AstFromPrimal $ astRFromS v
astRFromS (Ast.AstSFromR v) = v  -- no information lost, so no checks
astRFromS v = Ast.AstRFromS v

astSFromR :: forall sh s r. (GoodScalar r, KnownShS sh, KnownNat (Rank sh))
          => AstTensor AstMethodLet s (TKR (Rank sh) r) -> AstTensor AstMethodLet s (TKS sh r)
astSFromR (AstConcrete _ t) =
  AstConcrete (FTKS knownShS FTKScalar) $ RepN $ Nested.rcastToShaped (unRepN t) Nested.knownShS
astSFromR (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astSFromR v
astSFromR (Ast.AstRFromS @sh1 v) =
  case sameShape @sh1 @sh of
    Just Refl -> v
    _ -> error "astSFromR: different ranks in SFromR(RFromS)"
astSFromR v = Ast.AstSFromR v

astPrimalPart :: TensorKind y
              => AstTensor AstMethodLet FullSpan y
              -> AstTensor AstMethodLet PrimalSpan y
astPrimalPart t = case t of
  Ast.AstScalar u -> Ast.AstScalar $ astPrimalPart u
  Ast.AstUnScalar u -> Ast.AstUnScalar $ astPrimalPart u
  Ast.AstPair t1 t2 -> astPair (astPrimalPart t1) (astPrimalPart t2)
  Ast.AstProject1 v -> astProject1 (astPrimalPart v)
  Ast.AstProject2 v -> astProject2 (astPrimalPart v)
  Ast.AstVar{} -> Ast.AstPrimalPart t  -- the only normal form
  Ast.AstFromPrimal v -> v
  Ast.AstD u _ -> u
  Ast.AstCond b a2 a3 -> astCond b (astPrimalPart a2) (astPrimalPart a3)
  Ast.AstReplicate k v -> astReplicate k (astPrimalPart v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, astPrimalPart v)
  Ast.AstLet var u v -> astLet var u (astPrimalPart v)

  AstN1R opCode u -> AstN1R opCode (astPrimalPart u)
  AstN2R opCode u v -> AstN2R opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstR1R opCode u -> Ast.AstR1R opCode (astPrimalPart u)
  Ast.AstR2R opCode u v -> Ast.AstR2R opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2R opCode u v -> Ast.AstI2R opCode (astPrimalPart u) (astPrimalPart v)
  AstSumOfListR args -> astSumOfList (map astPrimalPart args)
  Ast.AstIndex v ix -> astIndexR (astPrimalPart v) ix
  Ast.AstSum v -> astSum (astPrimalPart v)
  Ast.AstScatter sh v (var, ix) -> astScatter sh (astPrimalPart v) (var, ix)
  Ast.AstFromVector l -> astFromVector (V.map astPrimalPart l)
  Ast.AstAppend x y -> astAppend (astPrimalPart x) (astPrimalPart y)
  Ast.AstSlice i k v -> astSlice i k (astPrimalPart v)
  Ast.AstReverse v -> astReverse (astPrimalPart v)
  Ast.AstTranspose perm v -> astTranspose perm (astPrimalPart v)
  Ast.AstReshape sh v -> astReshape sh (astPrimalPart v)
  Ast.AstGather sh v (vars, ix) -> astGatherR sh (astPrimalPart v) (vars, ix)
  Ast.AstCast v -> astCast $ astPrimalPart v
  Ast.AstProjectR l p -> astProjectR (astPrimalPart l) p
  Ast.AstLetHVectorIn vars l v -> astLetHVectorIn vars l (astPrimalPart v)
  Ast.AstRFromS v -> astRFromS $ astPrimalPart v

  AstN1S opCode u -> AstN1S opCode (astPrimalPart u)
  AstN2S opCode u v -> AstN2S opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astPrimalPart u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (astPrimalPart u)
                                             (astPrimalPart v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (astPrimalPart u)
                                             (astPrimalPart v)
  AstSumOfListS args -> astSumOfListS (map astPrimalPart args)
  Ast.AstIndexS v ix -> Ast.AstIndexS (astPrimalPart v) ix
  Ast.AstSumS v -> astSumS (astPrimalPart v)
  Ast.AstScatterS v (var, ix) -> astScatterS (astPrimalPart v) (var, ix)
  Ast.AstFromVectorS l -> astFromVectorS (V.map astPrimalPart l)
  Ast.AstAppendS x y -> astAppendS (astPrimalPart x) (astPrimalPart y)
  Ast.AstSliceS @i v -> astSliceS @i (astPrimalPart v)
  Ast.AstReverseS v -> astReverseS (astPrimalPart v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astPrimalPart v)
  Ast.AstReshapeS v -> astReshapeS (astPrimalPart v)
  Ast.AstGatherS v (vars, ix) -> astGatherS (astPrimalPart v) (vars, ix)
  Ast.AstCastS v -> astCastS $ astPrimalPart v
  Ast.AstProjectS l p -> astProjectS (astPrimalPart l) p
  Ast.AstNestS v -> astNestS $ astPrimalPart v
  Ast.AstUnNestS v -> astUnNestS $ astPrimalPart v
  Ast.AstSFromR v -> astSFromR $ astPrimalPart v

  Ast.AstMkHVector{} -> Ast.AstPrimalPart t  -- TODO
  Ast.AstApply v ll -> astHApply v (astPrimalPart ll)
  Ast.AstBuildHVector1 k (var, v) ->
    Ast.AstBuildHVector1 k (var, astPrimalPart v)
  Ast.AstMapAccumRDer @_ @_ @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs) ->
      Ast.AstMapAccumRDer k accShs bShs eShs f df rf
                          (astPrimalPart acc0) (astPrimalPart es)
  Ast.AstMapAccumLDer @_ @_ @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs) ->
      Ast.AstMapAccumRDer k accShs bShs eShs f df rf
                          (astPrimalPart acc0) (astPrimalPart es)
  _ -> error "TODO"

-- Note how this can't be pushed down, say, multiplication, because it
-- multiplies the dual part by the primal part. Addition is fine, though.
astDualPart :: TensorKind y
            => AstTensor AstMethodLet FullSpan y
            -> AstTensor AstMethodLet DualSpan y
astDualPart t = case t of
  Ast.AstScalar u -> Ast.AstScalar $ astDualPart u
  Ast.AstUnScalar u -> Ast.AstUnScalar $ astDualPart u
  Ast.AstPair t1 t2 -> astPair (astDualPart t1) (astDualPart t2)
  Ast.AstProject1 v -> astProject1 (astDualPart v)
  Ast.AstProject2 v -> astProject2 (astDualPart v)
  Ast.AstVar{} -> Ast.AstDualPart t
  Ast.AstFromPrimal{}  -> Ast.AstDualPart t  -- this equals nil (not primal 0)
  Ast.AstD _ u' -> u'
  Ast.AstCond b a2 a3 -> astCond b (astDualPart a2) (astDualPart a3)
  Ast.AstReplicate k v -> astReplicate k (astDualPart v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, astDualPart v)
  Ast.AstLet var u v -> astLet var u (astDualPart v)

  AstN1R{} -> Ast.AstDualPart t  -- stuck; the ops are not defined on dual part
  AstN2R{} -> Ast.AstDualPart t  -- stuck; the ops are not defined on dual part
  Ast.AstR1R{} -> Ast.AstDualPart t
  Ast.AstR2R{} -> Ast.AstDualPart t
  Ast.AstI2R{} -> Ast.AstDualPart t
  AstSumOfListR args -> astSumOfList (map astDualPart args)
  Ast.AstIndex v ix -> astIndexR (astDualPart v) ix
  Ast.AstSum v -> astSum (astDualPart v)
  Ast.AstScatter sh v (var, ix) -> astScatter sh (astDualPart v) (var, ix)
  Ast.AstFromVector l -> astFromVector (V.map astDualPart l)
  Ast.AstAppend x y -> astAppend (astDualPart x) (astDualPart y)
  Ast.AstSlice i k v -> astSlice i k (astDualPart v)
  Ast.AstReverse v -> astReverse (astDualPart v)
  Ast.AstTranspose perm v -> astTranspose perm (astDualPart v)
  Ast.AstReshape sh v -> astReshape sh (astDualPart v)
  Ast.AstGather sh v (vars, ix) -> astGatherR sh (astDualPart v) (vars, ix)
  Ast.AstCast v -> astCast $ astDualPart v
  Ast.AstProjectR l p -> astProjectR (astDualPart l) p
  Ast.AstLetHVectorIn vars l v -> astLetHVectorIn vars l (astDualPart v)
  Ast.AstRFromS v -> astRFromS $ astDualPart v

  AstN1S{} -> Ast.AstDualPart t
  AstN2S{} -> Ast.AstDualPart t
  Ast.AstR1S{} -> Ast.AstDualPart t
  Ast.AstR2S{} -> Ast.AstDualPart t
  Ast.AstI2S{} -> Ast.AstDualPart t
  AstSumOfListS args -> astSumOfListS (map astDualPart args)
  Ast.AstIndexS v ix -> Ast.AstIndexS (astDualPart v) ix
  Ast.AstSumS v -> astSumS (astDualPart v)
  Ast.AstScatterS v (var, ix) -> astScatterS (astDualPart v) (var, ix)
  Ast.AstFromVectorS l -> astFromVectorS (V.map astDualPart l)
  Ast.AstAppendS x y -> astAppendS (astDualPart x) (astDualPart y)
  Ast.AstSliceS @i v -> astSliceS @i (astDualPart v)
  Ast.AstReverseS v -> astReverseS (astDualPart v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astDualPart v)
  Ast.AstReshapeS v -> astReshapeS (astDualPart v)
  Ast.AstGatherS v (vars, ix) -> astGatherS (astDualPart v) (vars, ix)
  Ast.AstCastS v -> astCastS $ astDualPart v
  Ast.AstProjectS l p -> astProjectS (astDualPart l) p
  Ast.AstNestS v -> astNestS $ astDualPart v
  Ast.AstUnNestS v -> astUnNestS $ astDualPart v
  Ast.AstSFromR v -> astSFromR $ astDualPart v

  Ast.AstMkHVector{} -> Ast.AstDualPart t  -- TODO
  Ast.AstApply v ll -> astHApply v (astDualPart ll)
  Ast.AstBuildHVector1 k (var, v) ->
    Ast.AstBuildHVector1 k (var, astDualPart v)
  Ast.AstMapAccumRDer @_ @_ @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs) ->
      Ast.AstMapAccumRDer k accShs bShs eShs f df rf
                          (astDualPart acc0) (astDualPart es)
  Ast.AstMapAccumLDer @_ @_ @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs) ->
      Ast.AstMapAccumRDer k accShs bShs eShs f df rf
                          (astDualPart acc0) (astDualPart es)
  _ -> error "TODO"

astHApply :: forall s x y. (AstSpan s, TensorKind x, TensorKind y)
          => AstHFun x y -> AstTensor AstMethodLet s x -> AstTensor AstMethodLet s y
astHApply t u = case t of
  Ast.AstLambda ~(var, _ftk, v) ->
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> astLet var u v
      _ -> Ast.AstApply t u

mapRankedShaped
  :: AstSpan s2
  => (forall n r. (KnownNat n, GoodScalar r)
      => AstVarName s (TKR n r) -> AstTensor AstMethodLet s2 (TKR n r) -> acc
      -> acc)
  -> (forall sh r. (KnownShS sh, GoodScalar r)
      => AstVarName s (TKS sh r) -> AstTensor AstMethodLet s2 (TKS sh r) -> acc
      -> acc)
  -> (AstDynamicVarName, AstDynamic AstMethodLet s2)
  -> acc
  -> acc
{-# INLINE mapRankedShaped #-}
mapRankedShaped fRanked fShaped
                vd@(AstDynamicVarName @ty @r3 @sh3 varId, d) acc = case d of
  DynamicRanked @r4 @n4 v3
    | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
    , Just Refl <- matchingRank @sh3 @n4
    , Just Refl <- testEquality (typeRep @r3) (typeRep @r4) ->
        fRanked (mkAstVarName varId) v3 acc
  DynamicShaped @r4 @sh4 v3
    | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
    , Just Refl <- sameShape @sh3 @sh4
    , Just Refl <- testEquality (typeRep @r3) (typeRep @r4) ->
        fShaped (mkAstVarName varId) v3 acc
  DynamicRankedDummy @r4 @sh4 _ _
    | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
    , Just Refl <- sameShape @sh3 @sh4
    , Just Refl <- testEquality (typeRep @r3) (typeRep @r4) ->
        withListSh (Proxy @sh3) $ \_ ->
          fRanked (mkAstVarName varId) (astRFromS @sh3 @_ @r3 (astReplicate0NS 0)) acc
  DynamicShapedDummy @r4 @sh4 _ _
    | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
    , Just Refl <- sameShape @sh3 @sh4
    , Just Refl <- testEquality (typeRep @r3) (typeRep @r4) ->
        fShaped @sh4 @r4 (mkAstVarName varId) (astReplicate0NS 0) acc
  _ -> error $ "mapRankedShaped: corrupted arguments"
               `showFailure`
               ( vd, typeRep @ty, typeRep @r3, shapeT @sh3
               , scalarDynamic d, rankDynamic d )

-- Inlining doesn't work for this let constructor, because it has many
-- variables, so we try to reduce it to another for which it works.
astLetHVectorIn
  :: forall s s2 z. (AstSpan s, AstSpan s2, TensorKind z)
  => [AstDynamicVarName] -> AstTensor AstMethodLet s TKUntyped
  -> AstTensor AstMethodLet s2 z
  -> AstTensor AstMethodLet s2 z
astLetHVectorIn vars l v = case v of
  Ast.AstConcrete{} -> v
  Ast.AstFromPrimal v0 -> Ast.AstFromPrimal $ astLetHVectorIn vars l v0
  Ast.AstVar _ var2 ->
    case elemIndex (varNameToAstVarId var2)
                   (map dynamicVarNameToAstVarId vars) of
      Just i | Just Refl <- sameAstSpan @s @s2 -> case stensorKind @z of
        STKScalar _ -> Ast.AstUnScalar $ astProjectR l i
        STKR SNat STKScalar{} -> astProjectR l i
        STKS sh STKScalar{} -> withKnownShS sh $ astProjectS l i
        STKX sh STKScalar{}-> withKnownShX sh $ error "TODO"
        STKProduct{} -> error "astLetHVectorIn: STKProduct"
        STKUntyped -> error "astLetHVectorIn: STKUntyped"
        _ -> error "TODO"
      _ -> v
  Ast.AstPrimalPart (Ast.AstVar _ var2) ->
    case elemIndex (varNameToAstVarId var2)
         (map dynamicVarNameToAstVarId vars) of
      Just i | Just Refl <- sameAstSpan @s @FullSpan -> case stensorKind @z of
        STKScalar _ -> Ast.AstUnScalar $ astPrimalPart $ astProjectR l i
        STKR SNat STKScalar{} -> astPrimalPart $ astProjectR l i
        STKS sh STKScalar{} -> withKnownShS sh $ astPrimalPart $ astProjectS l i
        STKX sh STKScalar{} -> withKnownShX sh $ error "TODO"
        STKProduct{} -> error "astLetHVectorIn: STKProduct"
        STKUntyped -> error "astLetHVectorIn: STKUntyped"
        _ -> error "TODO"
      _ -> v
  Ast.AstDualPart (Ast.AstVar _ var2) ->
    case elemIndex (varNameToAstVarId var2)
         (map dynamicVarNameToAstVarId vars) of
      Just i | Just Refl <- sameAstSpan @s @FullSpan -> case stensorKind @z of
        STKScalar _ -> Ast.AstUnScalar $ astDualPart $ astProjectR l i
        STKR SNat STKScalar{} -> astDualPart $ astProjectR l i
        STKS sh STKScalar{} -> withKnownShS sh $ astDualPart $ astProjectS l i
        STKX sh STKScalar{} -> withKnownShX sh $ error "TODO"
        STKProduct{} -> error "astLetHVectorIn: STKProduct"
        STKUntyped -> error "astLetHVectorIn: STKUntyped"
        _ -> error "TODO"
      _ -> v
  _ -> case l of
        Ast.AstMkHVector l3 ->
          foldr (mapRankedShaped astLet astLet) v (zip vars (V.toList l3))
        Ast.AstFromPrimal (Ast.AstMkHVector l3) ->
          let clet varC uC vC = astLet varC (Ast.AstFromPrimal uC) vC
          in foldr (mapRankedShaped clet clet)
                   v (zip vars (V.toList l3))
        Ast.AstLetHVectorIn varsN lN (Ast.AstMkHVector l3) ->
          astLetHVectorIn varsN lN
          $ foldr (mapRankedShaped astLet astLet) v (zip vars (V.toList l3))
        Ast.AstFromPrimal (Ast.AstLetHVectorIn
                           varsN lN (Ast.AstMkHVector l3)) ->
          let clet varC uC vC = astLet varC (Ast.AstFromPrimal uC) vC
          in astLetHVectorIn varsN lN
             $ foldr (mapRankedShaped clet clet)
                     v (zip vars (V.toList l3))
        Ast.AstLet var2 u2 d2 ->
          astLet var2 u2
          $ astLetHVectorIn vars d2 v
{- TODO: convert vars? do more generally?
        Ast.AstFromPrimal (Ast.AstLet var2 u2 d2) ->
          astLet var2 (Ast.AstFromPrimal u2)
          $ astLetHVectorIn vars (Ast.AstFromPrimal d2) v
-}
        _ ->
          if astIsSmall True l || length vars == 1
          then let mkLet :: Int
                         -> AstDynamicVarName
                         -> AstTensor AstMethodLet s2 z
                         -> AstTensor AstMethodLet s2 z
                   mkLet i (AstDynamicVarName @ty @r3 @sh3 varId)
                     | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
                     , Dict <- lemKnownNatRank (knownShS @sh3) =
                       astLet (mkAstVarName @s @(TKR (Rank sh3) r3) varId)
                              (astProjectR l i)
                     | otherwise =
                       astLet (mkAstVarName @s @(TKS sh3 r3) varId)
                              (astProjectS l i)
               in ifoldr mkLet v vars
          else Ast.AstLetHVectorIn vars l v

-- TODO: a new section for this one?
astLetFun :: forall y z s s2.
             (TensorKind y, TensorKind z, AstSpan s, AstSpan s2)
          => AstTensor AstMethodLet s y -> (AstTensor AstMethodLet s y -> AstTensor AstMethodLet s2 z)
          -> AstTensor AstMethodLet s2 z
astLetFun a f | astIsSmall True a = f a  -- TODO: since astLetFun is now called recursively a lot, ensure astIsSmall is constant, at least except for a constant number of the recursive calls
astLetFun a f =
  let sh = ftkAst a
      (var, ast) = funToAst sh f
  in astLet var a ast  -- safe, because subsitution ruled out above


-- * The simplifying bottom-up pass

simplifyAstInt :: AstInt AstMethodLet -> AstInt AstMethodLet
simplifyAstInt = simplifyAst

simplifyAstIndex :: AstIndex AstMethodLet n -> AstIndex AstMethodLet n
simplifyAstIndex = fmap simplifyAstInt

simplifyAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
simplifyAstIxS = fmap simplifyAstInt

-- | This function guarantees full simplification: every redex
-- is visited and each combinator applied. The most exhaustive and costly
-- variants of each combinator are used, e.g., astIndexR.
simplifyAst
  :: forall s y. (AstSpan s, TensorKind y)
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
simplifyAst t = case t of
  Ast.AstScalar u -> Ast.AstScalar $ simplifyAst u
  Ast.AstUnScalar u -> Ast.AstUnScalar $ simplifyAst u
  Ast.AstPair t1 t2 -> astPair (simplifyAst t1) (simplifyAst t2)
  Ast.AstProject1 v -> astProject1 (simplifyAst v)
  Ast.AstProject2 v -> astProject2 (simplifyAst v)
  Ast.AstVar{} -> t
  Ast.AstPrimalPart v -> astPrimalPart (simplifyAst v)
  Ast.AstDualPart v -> astDualPart (simplifyAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (simplifyAst v)
  Ast.AstD u u' -> Ast.AstD (simplifyAst u) (simplifyAst u')
  Ast.AstCond b a2 a3 ->
    astCond (simplifyAstBool b) (simplifyAst a2) (simplifyAst a3)
  Ast.AstReplicate k v -> astReplicate k (simplifyAst v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, simplifyAst v)
  Ast.AstLet var u v -> astLet var (simplifyAst u) (simplifyAst v)
  AstConcrete{} -> t

  Ast.AstMinIndex a -> Ast.AstMinIndex (simplifyAst a)
  Ast.AstMaxIndex a -> Ast.AstMaxIndex (simplifyAst a)
  Ast.AstFloor a -> Ast.AstFloor (simplifyAst a)
  Ast.AstIota -> t
  AstN1R opCode u -> AstN1R opCode (simplifyAst u)
  AstN2R opCode u v -> AstN2R opCode (simplifyAst u) (simplifyAst v)
  Ast.AstR1R opCode u -> Ast.AstR1R opCode (simplifyAst u)
  Ast.AstR2R opCode u v -> Ast.AstR2R opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2R opCode u v -> Ast.AstI2R opCode (simplifyAst u) (simplifyAst v)
  AstSumOfListR args -> astSumOfList (map simplifyAst args)
  Ast.AstIndex v ix -> astIndexR (simplifyAst v) (simplifyAstIndex ix)
  Ast.AstSum v -> astSum (simplifyAst v)
  Ast.AstScatter sh v (var, ix) ->
    astScatter sh (simplifyAst v) (var, simplifyAstIndex ix)
  Ast.AstFromVector l -> astFromVector (V.map simplifyAst l)
  Ast.AstAppend x y -> astAppend (simplifyAst x) (simplifyAst y)
  Ast.AstSlice i k v -> astSlice i k (simplifyAst v)
  Ast.AstReverse v -> astReverse (simplifyAst v)
  Ast.AstTranspose perm v ->
    astTranspose (normalizePermutation perm) (simplifyAst v)
  Ast.AstReshape sh v -> astReshape sh (simplifyAst v)
  Ast.AstGather sh v (vars, ix) ->
    astGatherR sh (simplifyAst v) (vars, simplifyAstIndex ix)
  Ast.AstCast v -> astCast $ simplifyAst v
  Ast.AstFromIntegral v -> astFromIntegral $ simplifyAst v
  Ast.AstProjectR l p -> astProjectR (simplifyAst l) p
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars (simplifyAst l) (simplifyAst v)
  Ast.AstRFromS v -> astRFromS $ simplifyAst v

  Ast.AstMinIndexS a -> Ast.AstMinIndexS (simplifyAst a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (simplifyAst a)
  Ast.AstFloorS a -> Ast.AstFloorS (simplifyAst a)
  Ast.AstIotaS -> t
  AstN1S opCode u ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp1 opCode (simplifyAst u)
      _ -> AstN1S opCode (simplifyAst u)
  AstN2S opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp2 opCode (simplifyAst u) (simplifyAst v)
      _ -> AstN2S opCode (simplifyAst u) (simplifyAst v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (simplifyAst u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2S opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstIntegralOp2 opCode (simplifyAst u) (simplifyAst v)
      _ -> Ast.AstI2S opCode (simplifyAst u) (simplifyAst v)
  AstSumOfListS args ->
    case isTensorInt t of
      Just Refl -> foldr1 contractAstPlusOp (map simplifyAst args)
      _ -> astSumOfListS (map simplifyAst args)
  Ast.AstIndexS v ix -> astIndexS (simplifyAst v) (simplifyAstIxS ix)
  Ast.AstSumS v -> astSumS (simplifyAst v)
  Ast.AstScatterS v (var, ix) ->
    astScatterS (simplifyAst v) (var, simplifyAstIxS ix)
  Ast.AstFromVectorS l -> astFromVectorS (V.map simplifyAst l)
  Ast.AstAppendS x y -> astAppendS (simplifyAst x) (simplifyAst y)
  Ast.AstSliceS @i v -> astSliceS @i (simplifyAst v)
  Ast.AstReverseS v -> astReverseS (simplifyAst v)
  Ast.AstTransposeS perm v -> astTransposeS perm $ simplifyAst v
  Ast.AstReshapeS v -> astReshapeS $ simplifyAst v
  Ast.AstGatherS v (vars, ix) ->
    astGatherS (simplifyAst v) (vars, simplifyAstIxS ix)
  Ast.AstCastS v -> astCastS $ simplifyAst v
  Ast.AstFromIntegralS v -> astFromIntegralS $ simplifyAst v
  Ast.AstProjectS l p -> astProjectS (simplifyAst l) p
  Ast.AstNestS v -> astNestS $ simplifyAst v
  Ast.AstUnNestS v -> astUnNestS $ simplifyAst v
  Ast.AstSFromR v -> astSFromR $ simplifyAst v

  Ast.AstMkHVector l -> Ast.AstMkHVector $ V.map simplifyAstDynamic l
  Ast.AstApply v ll -> astHApply (simplifyAstHFun v)
                                  (simplifyAst ll)
  Ast.AstBuildHVector1 k (var, v) ->
    Ast.AstBuildHVector1 k (var, simplifyAst v)
  Ast.AstMapAccumRDer @accShs @bShs @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfAD (stensorKind @accShs)
    , Dict <- lemTensorKindOfAD (stensorKind @bShs)
    , Dict <- lemTensorKindOfAD (stensorKind @eShs) ->
      Ast.AstMapAccumRDer k accShs bShs eShs
                          (simplifyAstHFun f)
                          (simplifyAstHFun df)
                          (simplifyAstHFun rf)
                          (simplifyAst acc0)
                          (simplifyAst es)
  Ast.AstMapAccumLDer @accShs @bShs @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfAD (stensorKind @accShs)
    , Dict <- lemTensorKindOfAD (stensorKind @bShs)
    , Dict <- lemTensorKindOfAD (stensorKind @eShs) ->
      Ast.AstMapAccumLDer k accShs bShs eShs
                          (simplifyAstHFun f)
                          (simplifyAstHFun df)
                          (simplifyAstHFun rf)
                          (simplifyAst acc0)
                          (simplifyAst es)
  _ -> error "TODO"

simplifyAstDynamic
  :: AstSpan s
  => AstDynamic AstMethodLet s -> AstDynamic AstMethodLet s
simplifyAstDynamic (DynamicRanked u) =
  DynamicRanked $ simplifyAst u
simplifyAstDynamic (DynamicShaped u) =
  DynamicShaped $ simplifyAst u
simplifyAstDynamic u@DynamicRankedDummy{} = u
simplifyAstDynamic u@DynamicShapedDummy{} = u

simplifyAstHFun :: TensorKind y => AstHFun x y -> AstHFun x y
simplifyAstHFun = \case
  Ast.AstLambda ~(vvars, ftk, l) ->
    Ast.AstLambda (vvars, ftk, simplifyAst l)

simplifyAstBool :: AstBool AstMethodLet -> AstBool AstMethodLet
simplifyAstBool t = case t of
  Ast.AstBoolNot (AstBoolConst b) -> AstBoolConst $ not b
  Ast.AstBoolNot arg -> Ast.AstBoolNot $ simplifyAstBool arg
  Ast.AstB2 opCodeBool arg1 arg2 ->
    contractAstB2 opCodeBool (simplifyAstBool arg1) (simplifyAstBool arg2)
  AstBoolConst{} -> t
  Ast.AstRel @y3 opCodeRel arg1 arg2 ->
    case stensorKind @y3 of
      STKS sh STKScalar{} -> withKnownShS sh $
        contractRelOp opCodeRel (simplifyAst arg1) (simplifyAst arg2)
      -- These expressions potentially represent large tensors that are
      -- expensive to compute even when constant so we simplify and ignore them,
      -- because computation should be done on GPU, not on CPU when simplifying;
      -- we'd need a flag to control how much we pre-compute.
      -- Anyway, because these tensors sometimes represent indexes,
      -- we simplify them a bit more than the shaped ones.
      _ -> Ast.AstRel opCodeRel (simplifyAst arg1) (simplifyAst arg2)


-- * The expanding (to gather expressions) bottom-up pass

expandAstInt :: AstInt AstMethodLet -> AstInt AstMethodLet
expandAstInt = expandAst

expandAstIndex :: AstIndex AstMethodLet n -> AstIndex AstMethodLet n
expandAstIndex = fmap expandAstInt

expandAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
expandAstIxS = fmap expandAstInt

expandAst
  :: forall s y. (AstSpan s, TensorKind y)
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
expandAst t = case t of
  Ast.AstScalar u -> Ast.AstScalar $ expandAst u
  Ast.AstUnScalar u -> Ast.AstUnScalar $ expandAst u
  Ast.AstPair t1 t2 -> astPair (expandAst t1) (expandAst t2)
  Ast.AstProject1 v -> astProject1 (expandAst v)
  Ast.AstProject2 v -> astProject2 (expandAst v)
  Ast.AstVar{} -> t
  Ast.AstPrimalPart v -> astPrimalPart (expandAst v)
  Ast.AstDualPart v -> astDualPart (expandAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (expandAst v)
  Ast.AstD u u' -> Ast.AstD (expandAst u) (expandAst u')
  Ast.AstCond b a2 a3 ->
    astCond (expandAstBool b) (expandAst a2) (expandAst a3)
  Ast.AstReplicate k v -> astReplicate k (expandAst v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, expandAst v)
  Ast.AstLet var u v -> astLet var (expandAst u) (expandAst v)
  AstConcrete{} -> t

  Ast.AstMinIndex a -> Ast.AstMinIndex (expandAst a)
  Ast.AstMaxIndex a -> Ast.AstMaxIndex (expandAst a)
  Ast.AstFloor a -> Ast.AstFloor (expandAst a)
  Ast.AstIota -> t
  AstN1R opCode u -> AstN1R opCode (expandAst u)
  AstN2R opCode u v -> AstN2R opCode (expandAst u) (expandAst v)
  Ast.AstR1R opCode u -> Ast.AstR1R opCode (expandAst u)
  Ast.AstR2R opCode u v -> Ast.AstR2R opCode (expandAst u) (expandAst v)
  Ast.AstI2R opCode u v -> Ast.AstI2R opCode (expandAst u) (expandAst v)
  AstSumOfListR args -> astSumOfList (map expandAst args)
  Ast.AstIndex v ix -> astIndexKnobsR (defaultKnobs {knobExpand = True})
                                      (expandAst v)
                                      (expandAstIndex ix)
  Ast.AstSum v -> astSum (expandAst v)
  Ast.AstScatter sh v (var, ix) ->
    astScatter sh (expandAst v) (var, expandAstIndex ix)
  Ast.AstFromVector l -> astFromVector (V.map expandAst l)
  Ast.AstAppend x y -> astAppend (expandAst x) (expandAst y)
  Ast.AstSlice i k v -> astSlice i k (expandAst v)
  Ast.AstReverse v -> astReverse (expandAst v)
  Ast.AstTranspose perm v -> case v of
    Ast.AstVar{} -> t  -- normal form
    Ast.AstFromPrimal Ast.AstVar{} -> t  -- normal form
    Ast.AstPrimalPart Ast.AstVar{} -> t  -- normal form
    Ast.AstDualPart Ast.AstVar{} -> t  -- normal form
    Ast.AstProject1 Ast.AstVar{} -> t  -- normal form
    Ast.AstProject2 Ast.AstVar{} -> t  -- normal form
    Ast.AstProjectR Ast.AstVar{} _ -> t  -- normal form
    Ast.AstReplicate{} -> t  -- normal form
      -- TODO: this nf is silly, but right now transposes of replicates
      -- are small OR.Arrays and equivalent gathers are large OR.Arrays,
      -- so this has to stay. Maybe we should contract gathers back
      -- to transposes of replicates (not only to replicates). Or maybe
      -- we should extend orthotope to any gather schemes, not only
      -- the simple ones.
    AstN1R _ w | isVar w -> t  -- normal form
    AstN2R _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstR1R _ w | isVar w -> t  -- normal form
    Ast.AstR2R _ x y | isVar x && isVar y -> t  -- normal form
    AstSumOfListR{} -> t  -- normal form
    Ast.AstScatter @_ @_ @p _ _ _ | length perm > valueOf @p -> t  -- nf
    _ ->  -- not nf, let's express all as a gather
      astTransposeAsGather (defaultKnobs {knobExpand = True})
                           (normalizePermutation perm)
                           (expandAst v)
        -- this is expensive but the only way to guarantee full simplification
  Ast.AstReshape sh v -> case v of
    Ast.AstVar{} -> t  -- normal form
    Ast.AstFromPrimal Ast.AstVar{} -> t  -- normal form
    Ast.AstPrimalPart Ast.AstVar{} -> t  -- normal form
    Ast.AstDualPart Ast.AstVar{} -> t  -- normal form
    Ast.AstProject1 Ast.AstVar{} -> t  -- normal form
    Ast.AstProject2 Ast.AstVar{} -> t  -- normal form
    Ast.AstProjectR Ast.AstVar{} _ -> t  -- normal form
    AstN1R _ w | isVar w -> t  -- normal form
    AstN2R _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstR1R _ w | isVar w -> t  -- normal form
    Ast.AstR2R _ x y | isVar x && isVar y -> t  -- normal form
    AstSumOfListR{} -> t  -- normal form
    Ast.AstScatter{} -> t  -- normal form
    _ ->  -- not nf, let's express all as a gather
      astReshapeAsGather (defaultKnobs {knobExpand = True})
                         sh
                         (expandAst v)
        -- this is expensive but the only way to guarantee full simplification
  Ast.AstGather sh v (vars, ix) ->
    astGatherKnobsR (defaultKnobs {knobExpand = True})
                    sh (expandAst v) (vars, expandAstIndex ix)
  Ast.AstCast v -> astCast $ expandAst v
  Ast.AstFromIntegral v -> astFromIntegral $ expandAst v
  Ast.AstProjectR l p -> astProjectR (expandAst l) p
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars (expandAst l) (expandAst v)
  Ast.AstRFromS v -> astRFromS $ expandAst v

  Ast.AstMinIndexS a -> Ast.AstMinIndexS (expandAst a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (expandAst a)
  Ast.AstFloorS a -> Ast.AstFloorS (expandAst a)
  Ast.AstIotaS -> t
  AstN1S opCode u ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp1 opCode (expandAst u)
      _ -> AstN1S opCode (expandAst u)
  AstN2S opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp2 opCode (expandAst u) (expandAst v)
      _ -> {- TODO: case opCode of
        TimesOp | Just Refl <- sameNat (Proxy @n) (Proxy @3) ->
          AstN2R opCode (simplifyAst u) (simplifyAst v)
            -- TODO: a workaround for interpretMatmul2 not yet generalized
            -- to gathers (and moved from AstInterpret here, ideally)
        _ -> -} AstN2S opCode (expandAst u) (expandAst v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (expandAst u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (expandAst u) (expandAst v)
  Ast.AstI2S opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstIntegralOp2 opCode (expandAst u) (expandAst v)
      _ -> Ast.AstI2S opCode (expandAst u) (expandAst v)
  AstSumOfListS args ->
    case isTensorInt t of
      Just Refl -> foldr1 contractAstPlusOp (map expandAst args)
      _ -> astSumOfListS (map expandAst args)
  Ast.AstIndexS v ix -> astIndexKnobsS (defaultKnobs {knobExpand = True})
                                       (expandAst v)
                                       (expandAstIxS ix)
  Ast.AstSumS v -> astSumS (expandAst v)
  Ast.AstScatterS v (var, ix) ->
    astScatterS (expandAst v) (var, expandAstIxS ix)
  Ast.AstFromVectorS l -> astFromVectorS (V.map expandAst l)
  Ast.AstAppendS x y -> astAppendS (expandAst x) (expandAst y)
  Ast.AstSliceS @i v -> astSliceS @i (expandAst v)
  Ast.AstReverseS v -> astReverseS (expandAst v)
  Ast.AstTransposeS perm v -> astTransposeS perm $ expandAst v
  Ast.AstReshapeS v -> astReshapeS $ expandAst v
  Ast.AstGatherS v (vars, ix) ->
    astGatherKnobsS (defaultKnobs {knobExpand = True})
                    (expandAst v) (vars, expandAstIxS ix)
  Ast.AstCastS v -> astCastS $ expandAst v
  Ast.AstFromIntegralS v -> astFromIntegralS $ expandAst v
  Ast.AstProjectS l p -> astProjectS (expandAst l) p
  Ast.AstNestS v -> astNestS $ expandAst v
  Ast.AstUnNestS v -> astUnNestS $ expandAst v
  Ast.AstSFromR v -> astSFromR $ expandAst v

  Ast.AstMkHVector l -> Ast.AstMkHVector $ V.map expandAstDynamic l
  Ast.AstApply v ll -> astHApply (expandAstHFun v)
                                  (expandAst ll)
  Ast.AstBuildHVector1 k (var, v) ->
    Ast.AstBuildHVector1 k (var, expandAst v)
  Ast.AstMapAccumRDer @accShs @bShs @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfAD (stensorKind @accShs)
    , Dict <- lemTensorKindOfAD (stensorKind @bShs)
    , Dict <- lemTensorKindOfAD (stensorKind @eShs) ->
      Ast.AstMapAccumRDer k accShs bShs eShs
                          (expandAstHFun f)
                          (expandAstHFun df)
                          (expandAstHFun rf)
                          (expandAst acc0)
                          (expandAst es)
  Ast.AstMapAccumLDer @accShs @bShs @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfAD (stensorKind @accShs)
    , Dict <- lemTensorKindOfAD (stensorKind @bShs)
    , Dict <- lemTensorKindOfAD (stensorKind @eShs) ->
      Ast.AstMapAccumLDer k accShs bShs eShs
                          (expandAstHFun f)
                          (expandAstHFun df)
                          (expandAstHFun rf)
                          (expandAst acc0)
                          (expandAst es)
  _ -> error "TODO"

expandAstDynamic
  :: AstSpan s
  => AstDynamic AstMethodLet s -> AstDynamic AstMethodLet s
expandAstDynamic (DynamicRanked u) =
  DynamicRanked $ expandAst u
expandAstDynamic (DynamicShaped u) =
  DynamicShaped $ expandAst u
expandAstDynamic u@DynamicRankedDummy{} = u
expandAstDynamic u@DynamicShapedDummy{} = u

expandAstHFun :: TensorKind y => AstHFun x y -> AstHFun x y
expandAstHFun = \case
  Ast.AstLambda ~(vvars, ftk, l) ->
    Ast.AstLambda (vvars, ftk, expandAst l)

expandAstBool :: AstBool AstMethodLet -> AstBool AstMethodLet
expandAstBool t = case t of
  Ast.AstBoolNot (AstBoolConst b) -> AstBoolConst $ not b
  Ast.AstBoolNot arg -> Ast.AstBoolNot $ expandAstBool arg
  Ast.AstB2 opCodeBool arg1 arg2 ->
    contractAstB2 opCodeBool (expandAstBool arg1) (expandAstBool arg2)
  AstBoolConst{} -> t
  Ast.AstRel @y3 opCodeRel arg1 arg2 ->
    case stensorKind @y3 of
      STKS sh STKScalar{} -> withKnownShS sh $
        contractRelOp opCodeRel (expandAst arg1) (expandAst arg2)
      -- These expressions potentially represent large tensors that are
      -- expensive to compute even when constant so we expand and ignore them,
      -- because computation should be done on GPU, not on CPU when expanding;
      -- we'd need a flag to control how much we pre-compute.
      -- Anyway, because these tensors sometimes represent indexes,
      -- we expand them a bit more than the shaped ones.
      _ -> Ast.AstRel opCodeRel (expandAst arg1) (expandAst arg2)


-- * Contraction of arithmetic and boolean operation terms

-- TODO: when we have more tests, try to limit this rewrite
-- (or only the first half) to Int64 at rank 0 and see if performance improves
-- even more.
contractRelOp :: (KnownShS sh, GoodScalar r)
              => OpCodeRel
              -> AstTensor AstMethodLet PrimalSpan (TKS sh r)
              -> AstTensor AstMethodLet PrimalSpan (TKS sh r)
              -> AstBool AstMethodLet
contractRelOp EqOp (AstConcrete _ u) (AstConcrete _ v) = AstBoolConst $ u == v
contractRelOp NeqOp (AstConcrete _ u) (AstConcrete _ v) = AstBoolConst $ u /= v
contractRelOp LeqOp (AstConcrete _ u) (AstConcrete _ v) = AstBoolConst $ u <= v
contractRelOp GeqOp (AstConcrete _ u) (AstConcrete _ v) = AstBoolConst $ u >= v
contractRelOp LsOp (AstConcrete _ u) (AstConcrete _ v) = AstBoolConst $ u < v
contractRelOp GtOp (AstConcrete _ u) (AstConcrete _ v) = AstBoolConst $ u > v
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
-- only tensors from inside bare AstConcrete and float tensors are always
-- wrapped in AstFromPrimal, so they can't be involved.
--
-- Rank has to be 0 so that the value expressions @0@ below don't crash.
--
-- Several first paragraphs are modelled on @Num@ instance for @AstRanked@
-- and depend on the normal form where @AstConcrete@, if any, is the first element
-- and the list if fully flattened and of length >= 2.
-- Additionally we here ensure the @AstConcrete@ is never zero.
--
-- Not considered are rules that would require comparing non-constant terms
-- or that would duplicate a non-constant term, as well as most rules
-- informed by inequalities, expressed via max or min, such as
-- max n (signum (abs x)) | n <= 0 --> signum (abs x).
-- We could use sharing via @tlet@ when terms are duplicated, but it's
-- unclear if the term bloat is worth it.
contractAstPlusOp :: AstInt AstMethodLet -> AstInt AstMethodLet -> AstInt AstMethodLet
contractAstPlusOp (AstSumOfListS (AstConcrete _ u : lu))
                  (AstSumOfListS (AstConcrete _ v : lv)) =
  addConstToList (u + v) (lu ++ lv)
contractAstPlusOp (AstSumOfListS lu)
                  (AstSumOfListS (AstConcrete ftk v : lv)) =
  AstSumOfListS (AstConcrete ftk v : lv ++ lu)
contractAstPlusOp (AstSumOfListS lu)
                  (AstSumOfListS lv) =
  AstSumOfListS (lu ++ lv)

contractAstPlusOp (AstConcrete _ u)
                  (AstSumOfListS (AstConcrete _ v : lv)) =
  addConstToList (u + v) lv
contractAstPlusOp u
                  (AstSumOfListS (AstConcrete ftk v : lv)) =
  AstSumOfListS (AstConcrete ftk v : u : lv)
contractAstPlusOp u
                  (AstSumOfListS lv) =
  AstSumOfListS (u : lv)

contractAstPlusOp (AstSumOfListS (AstConcrete _ u : lu))
                  (AstConcrete _ v) =
  addConstToList (u + v) lu
contractAstPlusOp (AstSumOfListS (AstConcrete ftk u : lu))
                  v =
  AstSumOfListS (AstConcrete ftk u : v : lu)
contractAstPlusOp (AstSumOfListS lu)
                  v =
  AstSumOfListS (v : lu)

contractAstPlusOp (AstConcrete ftk u) (AstConcrete _ v) = AstConcrete ftk $ u + v
contractAstPlusOp u (AstConcrete _ v) = addConstToList v [u]
contractAstPlusOp (AstConcrete _ u) v = addConstToList u [v]

-- Unfortunately, these won't fire if the required terms are scattered
-- among elements of the AstSumOfListS list. However, in many cases,
-- binary addition is used interspersed with other operations,
-- so longer lists don't form and so these terms have a chance to be adjacent,
-- especially that AstConcrete is guaranteed not to intervene.
contractAstPlusOp (AstN1S NegateOp (Ast.AstVar _ var))
                  (Ast.AstVar _ var')
  | var == var' = 0
contractAstPlusOp (Ast.AstVar _ var')
                  (AstN1S NegateOp (Ast.AstVar _ var))
  | var == var' = 0
contractAstPlusOp
  (Ast.AstI2S RemOp (AstN1S NegateOp (Ast.AstVar _ var)) (AstConcrete _ v))
  (Ast.AstI2S RemOp (Ast.AstVar _ var') (AstConcrete _ v'))
  | var == var' && v == v' = 0
contractAstPlusOp
  (Ast.AstI2S RemOp (Ast.AstVar _ var') (AstConcrete _ v'))
  (Ast.AstI2S RemOp (AstN1S NegateOp (Ast.AstVar _ var)) (AstConcrete _ v))
  | var == var' && v == v' = 0

contractAstPlusOp u v = AstSumOfListS [u, v]

addConstToList :: RepN (TKS '[] Int64) -> [AstInt AstMethodLet] -> AstInt AstMethodLet
addConstToList _ [] = error "addConstToList: AstSumOfListS list too short"
addConstToList arr [i] =
  if Nested.sunScalar (unRepN arr) == 0 then i else AstSumOfListS [AstConcrete (FTKS knownShS FTKScalar) arr, i]
addConstToList arr l =
  if Nested.sunScalar (unRepN arr) == 0 then AstSumOfListS l else AstSumOfListS (AstConcrete (FTKS knownShS FTKScalar) arr : l)

contractAstNumOp1 :: OpCodeNum1 -> AstInt AstMethodLet -> AstInt AstMethodLet
contractAstNumOp1 NegateOp (AstConcrete ftk u) = AstConcrete ftk $ negate u
contractAstNumOp1 NegateOp (AstSumOfListS l) =
  foldr1 contractAstPlusOp (map (contractAstNumOp1 NegateOp) l)
contractAstNumOp1 NegateOp (AstN2S TimesOp (AstConcrete ftk u) v) =
  contractAstNumOp2 TimesOp (AstConcrete ftk $ negate u) v
    -- given a choice, prefer to negate a constant
contractAstNumOp1 NegateOp (AstN2S TimesOp u v) =
  contractAstNumOp2 TimesOp u (contractAstNumOp1 NegateOp v)
contractAstNumOp1 NegateOp (AstN1S NegateOp u) = u
contractAstNumOp1 NegateOp (AstN1S SignumOp u) =
  contractAstNumOp1 SignumOp (contractAstNumOp1 NegateOp u)
contractAstNumOp1 NegateOp (Ast.AstI2S QuotOp u v) =
  contractAstIntegralOp2 QuotOp (contractAstNumOp1 NegateOp u) v
    -- v is likely positive and let's keep it so
contractAstNumOp1 NegateOp (Ast.AstI2S RemOp u v) =
  contractAstIntegralOp2 RemOp (contractAstNumOp1 NegateOp u) v
    -- v is likely positive and let's keep it so

contractAstNumOp1 AbsOp (AstConcrete ftk u) = AstConcrete ftk $ abs u
contractAstNumOp1 AbsOp (AstN1S AbsOp u) = AstN1S AbsOp u
contractAstNumOp1 AbsOp (AstN1S NegateOp u) = contractAstNumOp1 AbsOp u
contractAstNumOp1 SignumOp (AstConcrete ftk u) = AstConcrete ftk $ signum u
contractAstNumOp1 SignumOp (AstN1S SignumOp u) = AstN1S SignumOp u
contractAstNumOp1 SignumOp (AstN1S AbsOp u) =
  contractAstNumOp1 AbsOp (AstN1S SignumOp u)

contractAstNumOp1 opCode u = AstN1S opCode u

contractAstNumOp2 :: OpCodeNum2 -> AstInt AstMethodLet -> AstInt AstMethodLet -> AstInt AstMethodLet
contractAstNumOp2 MinusOp u v =
  contractAstPlusOp u (contractAstNumOp1 NegateOp v)
contractAstNumOp2 TimesOp (AstConcrete ftk u) (AstConcrete _ v) = AstConcrete ftk $ u * v
contractAstNumOp2 TimesOp (AstConcrete ftk i) _v | Nested.sunScalar (unRepN i) == 0 = AstConcrete ftk i
contractAstNumOp2 TimesOp _u (AstConcrete ftk i) | Nested.sunScalar (unRepN i) == 0 = AstConcrete ftk i
contractAstNumOp2 TimesOp (AstConcrete _ i) v | Nested.sunScalar (unRepN i) == 1 = v
contractAstNumOp2 TimesOp u (AstConcrete _ i) | Nested.sunScalar (unRepN i) == 1 = u
{- TODO: is it worth adding AstLet with a fresh variables
   to share w and so make these rules safe? Perhaps after we decide
   a normal form (e.g., a polynomial)?
contractAstNumOp TimesOp (AstN2S PlusOp (u, v), w) =
  contractAstPlusOp ( contractAstNumOp TimesOp (u, w)
                    , contractAstNumOp TimesOp (v, w) )
contractAstNumOp TimesOp (u, AstN2S PlusOp (v, w)) =
  contractAstPlusOp ( contractAstNumOp TimesOp (u, v)
                    , contractAstNumOp TimesOp (u, w) )
-}
contractAstNumOp2 TimesOp (AstSumOfListS l) w@AstConcrete{} =
  foldr1 contractAstPlusOp (map (\u -> contractAstNumOp2 TimesOp u w) l)
contractAstNumOp2 TimesOp u@AstConcrete{} (AstSumOfListS l) =
  foldr1 contractAstPlusOp (map (contractAstNumOp2 TimesOp u) l)
-- TODO: perhaps aim for a polynomial normal form? but that requires global
-- inspection of the whole expression
contractAstNumOp2 TimesOp (AstConcrete ftk u) (AstN2S TimesOp (AstConcrete _ v) w) =
  contractAstNumOp2 TimesOp (AstConcrete ftk $ u * v) w
contractAstNumOp2 TimesOp u (AstConcrete ftk n) =
  contractAstNumOp2 TimesOp (AstConcrete ftk n) u
contractAstNumOp2 TimesOp (AstN2S TimesOp u v) w =
  contractAstNumOp2 TimesOp u (contractAstNumOp2 TimesOp v w)

-- With static shapes, the second argument to QuotOp and RemOp
-- is often a constant, which makes such rules worth including,
-- since they are likely to fire. To help them fire, we avoid changing
-- that constant, if possible, e.g., in rules for NegateOp.
contractAstNumOp2
  TimesOp (AstConcrete ftk v)
          (Ast.AstI2S QuotOp (Ast.AstVar sh var) (AstConcrete _ v')) | v == v' =
    contractAstNumOp2 MinusOp
                      (Ast.AstVar sh var)
                      (Ast.AstI2S RemOp (Ast.AstVar sh var) (AstConcrete ftk v))
contractAstNumOp2 opCode u v = AstN2S opCode u v

contractAstIntegralOp2 :: OpCodeIntegral2 -> AstInt AstMethodLet -> AstInt AstMethodLet -> AstInt AstMethodLet
contractAstIntegralOp2 QuotOp (AstConcrete ftk u) (AstConcrete _ v) = AstConcrete ftk $ quotF u v
contractAstIntegralOp2 QuotOp (AstConcrete ftk i) _v | Nested.sunScalar (unRepN i) == 0 = AstConcrete ftk i
contractAstIntegralOp2 QuotOp u (AstConcrete _ i) | Nested.sunScalar (unRepN i) == 1 = u
contractAstIntegralOp2 QuotOp (Ast.AstI2S RemOp _u (AstConcrete _ v)) (AstConcrete _ v')
  | v' >= v && v >= 0 = 0
contractAstIntegralOp2 QuotOp (Ast.AstI2S QuotOp u v) w =
  contractAstIntegralOp2 QuotOp u (contractAstNumOp2 TimesOp v w)
contractAstIntegralOp2 QuotOp (Ast.AstN2S TimesOp (AstConcrete _ u) v) (AstConcrete _ u')
  | u == u' = v

contractAstIntegralOp2 RemOp (AstConcrete ftk u) (AstConcrete _ v) = AstConcrete ftk $ remF u v
contractAstIntegralOp2 RemOp (AstConcrete ftk i) _v | Nested.sunScalar (unRepN i) == 0 = AstConcrete ftk i
contractAstIntegralOp2 RemOp _u (AstConcrete ftk i) | Nested.sunScalar (unRepN i) == 1 = AstConcrete ftk $ RepN $ Nested.sscalar 0
contractAstIntegralOp2 RemOp (Ast.AstI2S RemOp u (AstConcrete ftk v)) (AstConcrete _ v')
  | v' >= v && v >= 0 = Ast.AstI2S RemOp u (AstConcrete ftk v)
contractAstIntegralOp2 RemOp (Ast.AstI2S RemOp u (AstConcrete ftk v)) (AstConcrete _ v')
  | remF v v' == 0 && v > 0 = contractAstIntegralOp2 RemOp u (AstConcrete ftk v')
contractAstIntegralOp2 RemOp (AstN2S TimesOp (AstConcrete _ u) _v) (AstConcrete _ u')
  | remF u u' == 0 = 0

contractAstIntegralOp2 opCode u v = Ast.AstI2S opCode u v

-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right.
contractAstB2 :: OpCodeBool -> AstBool AstMethodLet -> AstBool AstMethodLet -> AstBool AstMethodLet
contractAstB2 AndOp (AstBoolConst True) b = b
contractAstB2 AndOp (AstBoolConst False) _b = AstBoolConst False
contractAstB2 AndOp b (AstBoolConst True) = b
contractAstB2 AndOp _b (AstBoolConst False) = AstBoolConst False
contractAstB2 OrOp (AstBoolConst True) _b = AstBoolConst True
contractAstB2 OrOp (AstBoolConst False) b = b
contractAstB2 OrOp _b (AstBoolConst True) = AstBoolConst True
contractAstB2 OrOp b (AstBoolConst False) = b
contractAstB2 opCodeBool arg1 arg2 = Ast.AstB2 opCodeBool arg1 arg2


-- * Substitution wrappers

substituteAst :: forall s s2 y z. (AstSpan s, AstSpan s2, TensorKind y, TensorKind z)
              => AstTensor AstMethodLet s2 z -> AstVarName s2 z
              -> AstTensor AstMethodLet s y
              -> AstTensor AstMethodLet s y
substituteAst i var v1 =
  fromMaybe v1 $ substitute1Ast i var v1

substituteAstIndex
  :: (AstSpan s2, KnownShS sh2, GoodScalar r2)
  => AstTensor AstMethodLet s2 (TKS sh2 r2) -> AstVarName s2 (TKS sh2 r2)
  -> AstIndex AstMethodLet n
  -> AstIndex AstMethodLet n
substituteAstIndex i var ix =
  fromMaybe ix $ substitute1AstIndex i var ix

substituteAstIxS
  :: (AstSpan s2, KnownShS sh2, GoodScalar r2)
  => AstTensor AstMethodLet s2 (TKS sh2 r2) -> AstVarName s2 (TKS sh2 r2)
  -> AstIxS AstMethodLet sh
  -> AstIxS AstMethodLet sh
substituteAstIxS i var  ix =
  fromMaybe ix $ substitute1AstIxS i var ix

substituteAstBool
  :: (AstSpan s2, TensorKind y)
  => AstTensor AstMethodLet s2 y -> AstVarName s2 y -> AstBool AstMethodLet
  -> AstBool AstMethodLet
substituteAstBool i var v1 =
  fromMaybe v1 $ substitute1AstBool i var v1


-- * Substitution workers

-- | We assume no variable is shared between a binding and its nested binding
-- and nobody substitutes into variables that are bound.
-- This keeps the substitution code simple, because we never need to compare
-- variables to any variable in the bindings.
substitute1Ast :: forall s s2 y z.
                  (AstSpan s, AstSpan s2, TensorKind y, TensorKind z)
               => AstTensor AstMethodLet s2 z -> AstVarName s2 z
               -> AstTensor AstMethodLet s y
               -> Maybe (AstTensor AstMethodLet s y)
substitute1Ast i var v1 = case v1 of
  Ast.AstScalar u -> Ast.AstScalar <$> substitute1Ast i var u
  Ast.AstUnScalar u -> Ast.AstUnScalar <$> substitute1Ast i var u
  Ast.AstPair u v ->
    case (substitute1Ast i var u, substitute1Ast i var v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) -> Just $ astPair (fromMaybe u mu) (fromMaybe v mv)
  Ast.AstProject1 a -> astProject1 <$> substitute1Ast i var a
  Ast.AstProject2 a -> astProject2 <$> substitute1Ast i var a
  Ast.AstVar sh var2 ->
    if varNameToAstVarId var == varNameToAstVarId var2
    then case sameAstSpan @s @s2 of
        Just Refl -> case sameTensorKind @y @z of
          Just Refl ->
            assert (ftkAst i == sh `blame` (ftkAst i, sh, i))
            Just i
          _ -> error $ "substitute1Ast: kind of the variable "
                       ++ show var2 ++ ": "
                       ++ show (stensorKind @y, sh)
                       ++ ", payload kind: "
                       ++ show (stensorKind @z, ftkAst i)
                       ++ ", payload: " ++ show i
        _ -> error "substitute1Ast: span"
    else Nothing
  Ast.AstPrimalPart a -> astPrimalPart <$> substitute1Ast i var a
  Ast.AstDualPart a -> astDualPart <$> substitute1Ast i var a
  Ast.AstFromPrimal a -> Ast.AstFromPrimal <$> substitute1Ast i var a
  Ast.AstD x y ->
    case (substitute1Ast i var x, substitute1Ast i var y) of
      (Nothing, Nothing) -> Nothing
      (mx, my) -> Just $ Ast.AstD (fromMaybe x mx) (fromMaybe y my)
  Ast.AstCond b v w ->
    case ( substitute1AstBool i var b
         , substitute1Ast i var v
         , substitute1Ast i var w ) of
      (Nothing, Nothing, Nothing) -> Nothing
      (mb, mv, mw) ->
        Just $ astCond (fromMaybe b mb) (fromMaybe v mv) (fromMaybe w mw)
  Ast.AstReplicate k v -> astReplicate k <$> substitute1Ast i var v
  Ast.AstBuild1 k (var2, v) ->
    Ast.AstBuild1 k . (var2,) <$> substitute1Ast i var v
  Ast.AstLet var2 u v ->
    case (substitute1Ast i var u, substitute1Ast i var v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) -> Just $ astLet var2 (fromMaybe u mu) (fromMaybe v mv)

  Ast.AstMinIndex a -> Ast.AstMinIndex <$> substitute1Ast i var a
  Ast.AstMaxIndex a -> Ast.AstMaxIndex <$> substitute1Ast i var a
  Ast.AstFloor a -> Ast.AstFloor <$> substitute1Ast i var a
  Ast.AstIota -> Nothing
  Ast.AstN1R opCode u -> Ast.AstN1R opCode  <$> substitute1Ast i var u
  Ast.AstN2R opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstN2R opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstR1R opCode u -> Ast.AstR1R opCode <$> substitute1Ast i var u
  Ast.AstR2R opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstR2R opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstI2R opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstI2R opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstSumOfListR args ->
    let margs = map (substitute1Ast i var) args
    in if any isJust margs
       then Just $ astSumOfList $ zipWith fromMaybe args margs
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
  Ast.AstAppend x y ->
    case (substitute1Ast i var x, substitute1Ast i var y) of
      (Nothing, Nothing) -> Nothing
      (mx, my) -> Just $ astAppend (fromMaybe x mx) (fromMaybe y my)
  Ast.AstSlice i2 n v -> astSlice i2 n <$> substitute1Ast i var v
  Ast.AstReverse v -> astReverse <$> substitute1Ast i var v
  Ast.AstTranspose perm v -> astTranspose perm <$> substitute1Ast i var v
  Ast.AstReshape sh v -> astReshape sh <$> substitute1Ast i var v
  Ast.AstGather sh v (vars, ix) ->
    case (substitute1Ast i var v, substitute1AstIndex i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astGatherR sh (fromMaybe v mv)
                                        (vars, fromMaybe ix mix)
  Ast.AstCast v -> astCast <$> substitute1Ast i var v
  Ast.AstFromIntegral v -> astFromIntegral <$> substitute1Ast i var v
  Ast.AstConcrete{} -> Nothing
  Ast.AstProjectR l p ->
    case substitute1Ast i var l of
      Nothing -> Nothing
      ml -> Just $ astProjectR (fromMaybe l ml) p
  Ast.AstLetHVectorIn vars l v ->
    case (substitute1Ast i var l, substitute1Ast i var v) of
      (Nothing, Nothing) -> Nothing
      (ml, mv) ->
        Just $ astLetHVectorIn vars (fromMaybe l ml) (fromMaybe v mv)
  Ast.AstRFromS v -> astRFromS <$> substitute1Ast i var v

  Ast.AstMinIndexS a -> Ast.AstMinIndexS <$> substitute1Ast i var a
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS <$> substitute1Ast i var a
  Ast.AstFloorS a -> Ast.AstFloorS <$> substitute1Ast i var a
  Ast.AstIotaS -> Nothing
  Ast.AstN1S opCode u ->
    (\u2 -> case isTensorInt u2 of
       Just Refl -> contractAstNumOp1 opCode u2
       _ -> Ast.AstN1S opCode u2)
    <$> substitute1Ast i var u
  Ast.AstN2S opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ case isTensorInt u of
         Just Refl -> contractAstNumOp2 opCode (fromMaybe u mu) (fromMaybe v mv)
         _ -> Ast.AstN2S opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstR1S opCode u -> Ast.AstR1S opCode <$> substitute1Ast i var u
  Ast.AstR2S opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstR2S opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstI2S opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ case isTensorInt u of
         Just Refl ->
           contractAstIntegralOp2 opCode (fromMaybe u mu) (fromMaybe v mv)
         _ -> Ast.AstI2S opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstSumOfListS args ->
    let margs = map (substitute1Ast i var) args
    in if any isJust margs
       then Just $ case isTensorInt v1 of
         Just Refl -> foldr1 contractAstPlusOp $ zipWith fromMaybe args margs
         _ -> astSumOfListS $ zipWith fromMaybe args margs
       else Nothing
  Ast.AstIndexS v ix ->
    case (substitute1Ast i var v, substitute1AstIxS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astIndexS (fromMaybe v mv) (fromMaybe ix mix)
  Ast.AstSumS v -> astSumS <$> substitute1Ast i var v
  Ast.AstScatterS v (vars, ix) ->
    case (substitute1Ast i var v, substitute1AstIxS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astScatterS (fromMaybe v mv)
                                      (vars, fromMaybe ix mix)
  Ast.AstFromVectorS args ->
    let margs = V.map (substitute1Ast i var) args
    in if V.any isJust margs
       then Just $ astFromVectorS $ V.zipWith fromMaybe args margs
       else Nothing
  Ast.AstAppendS x y ->
    case (substitute1Ast i var x, substitute1Ast i var y) of
      (Nothing, Nothing) -> Nothing
      (mx, my) -> Just $ astAppendS (fromMaybe x mx) (fromMaybe y my)
  Ast.AstSliceS @i v -> astSliceS @i <$> substitute1Ast i var v
  Ast.AstReverseS v -> astReverseS <$> substitute1Ast i var v
  Ast.AstTransposeS perm v -> astTransposeS perm <$> substitute1Ast i var v
  Ast.AstReshapeS v -> astReshapeS <$> substitute1Ast i var v
  Ast.AstGatherS v (vars, ix) ->
    case (substitute1Ast i var v, substitute1AstIxS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astGatherS (fromMaybe v mv)
                                     (vars, fromMaybe ix mix)
  Ast.AstCastS v -> astCastS <$> substitute1Ast i var v
  Ast.AstFromIntegralS a -> astFromIntegralS <$> substitute1Ast i var a
  Ast.AstProjectS l p ->
    case substitute1Ast i var l of
      Nothing -> Nothing
      ml -> Just $ astProjectS (fromMaybe l ml) p
  Ast.AstNestS v -> astNestS <$> substitute1Ast i var v
  Ast.AstUnNestS v -> astUnNestS <$> substitute1Ast i var v
  Ast.AstSFromR v -> astSFromR <$> substitute1Ast i var v

  Ast.AstMkHVector args ->
    let margs = V.map (substitute1AstDynamic i var) args
    in if V.any isJust margs
       then Just $ Ast.AstMkHVector $ V.zipWith fromMaybe args margs
       else Nothing
  Ast.AstApply t ll ->
    case ( substitute1AstHFun i var t
         , substitute1Ast i var ll ) of
      (Nothing, Nothing) -> Nothing
      (mt, mll) -> Just $ astHApply (fromMaybe t mt) (fromMaybe ll mll)
  Ast.AstBuildHVector1 k (var2, v) ->
    Ast.AstBuildHVector1 k . (var2,) <$> substitute1Ast i var v
  Ast.AstMapAccumRDer @accShs @bShs @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfAD (stensorKind @accShs)
    , Dict <- lemTensorKindOfAD (stensorKind @bShs)
    , Dict <- lemTensorKindOfAD (stensorKind @eShs) ->
      case ( substitute1AstHFun i var f, substitute1AstHFun i var df
           , substitute1AstHFun i var rf, substitute1Ast i var acc0
           , substitute1Ast i var es ) of
        (Nothing, Nothing, Nothing, Nothing, Nothing) -> Nothing
        (mf, mdf, mrf, macc0, mes) ->
          Just $ Ast.AstMapAccumRDer k accShs bShs eShs
                                     (fromMaybe f mf)
                                     (fromMaybe df mdf)
                                     (fromMaybe rf mrf)
                                     (fromMaybe acc0 macc0)
                                     (fromMaybe es mes)
  Ast.AstMapAccumLDer @accShs @bShs @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfAD (stensorKind @accShs)
    , Dict <- lemTensorKindOfAD (stensorKind @bShs)
    , Dict <- lemTensorKindOfAD (stensorKind @eShs) ->
      case ( substitute1AstHFun i var f, substitute1AstHFun i var df
           , substitute1AstHFun i var rf, substitute1Ast i var acc0
           , substitute1Ast i var es ) of
        (Nothing, Nothing, Nothing, Nothing, Nothing) -> Nothing
        (mf, mdf, mrf, macc0, mes) ->
          Just $ Ast.AstMapAccumLDer k accShs bShs eShs
                                     (fromMaybe f mf)
                                     (fromMaybe df mdf)
                                     (fromMaybe rf mrf)
                                     (fromMaybe acc0 macc0)
                                     (fromMaybe es mes)
  _ -> error "TODO"

substitute1AstIndex
  :: (AstSpan s2, TensorKind y)
  => AstTensor AstMethodLet s2 y -> AstVarName s2 y -> AstIndex AstMethodLet n
  -> Maybe (AstIndex AstMethodLet n)
substitute1AstIndex i var ix =
  let mix = fmap (substitute1Ast i var) ix
  in if any isJust mix
     then Just $ zipWith_Index fromMaybe ix mix
     else Nothing

substitute1AstIxS
  :: (AstSpan s2, TensorKind y)
  => AstTensor AstMethodLet s2 y -> AstVarName s2 y -> AstIxS AstMethodLet sh
  -> Maybe (AstIxS AstMethodLet sh)
substitute1AstIxS i var ix =
  let mix = fmap (substitute1Ast i var) ix
  in if any isJust mix
     then Just $ ShapedList.zipWith_Index fromMaybe ix mix
     else Nothing

substitute1AstDynamic
  :: (AstSpan s, AstSpan s2, TensorKind y)
  => AstTensor AstMethodLet s2 y -> AstVarName s2 y -> AstDynamic AstMethodLet s
  -> Maybe (AstDynamic AstMethodLet s)
substitute1AstDynamic i var = \case
  DynamicRanked t ->
    DynamicRanked <$> substitute1Ast i var t
  DynamicShaped t ->
    DynamicShaped <$> substitute1Ast i var t
  DynamicRankedDummy{} -> Nothing
  DynamicShapedDummy{} -> Nothing

substitute1AstHFun
  :: forall s2 x y z.
     AstTensor AstMethodLet s2 z -> AstVarName s2 z -> AstHFun x y
  -> Maybe (AstHFun x y)
substitute1AstHFun _i _var = \case
  Ast.AstLambda{} -> Nothing  -- no outside free variables

substitute1AstBool :: (AstSpan s2, TensorKind y)
                   => AstTensor AstMethodLet s2 y -> AstVarName s2 y -> AstBool AstMethodLet
                   -> Maybe (AstBool AstMethodLet)
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
  Ast.AstRel @y3 opCodeRel arg1 arg2 ->
    let mr1 = substitute1Ast i var arg1
        mr2 = substitute1Ast i var arg2
    in if isJust mr1 || isJust mr2
       then case stensorKind @y3 of
         STKS sh STKScalar{} -> withKnownShS sh $
           Just $ contractRelOp opCodeRel (fromMaybe arg1 mr1)
                                          (fromMaybe arg2 mr2)
         _ -> Just $ Ast.AstRel opCodeRel (fromMaybe arg1 mr1)
                                          (fromMaybe arg2 mr2)
       else Nothing
