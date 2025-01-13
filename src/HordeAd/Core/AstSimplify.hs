{-# LANGUAGE AllowAmbiguousTypes, TupleSections #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=100 #-}
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
  ( -- * The combinators for indexing and gather
    astNonIndexStep, astIndexStep, astIndexStepS
  , astGatherStep, astGatherStepS
    -- * The simplifying combinators, one for most AST constructors
  , astFromScalar
  , astPair, astLet, astCond, astSumOfList
  , astFromVector, astSum, astScatter, astScatterS
  , astReplicate, astAppend, astAppendS, astSlice, astSliceS
  , astReverse, astReverseS
  , astTranspose, astTransposeS, astReshape, astReshapeS
  , astCast, astCastR, astCastS
  , astFromIntegral, astFromIntegralR, astFromIntegralS
  , astProject1, astProject2, astProjectR, astProjectS
  , astPrimalPart, astDualPart
  , astRFromS, astSFromR, astSFromX, astXFromS
  , astXNestR, astXNestS, astXNest, astXUnNestR, astXUnNestS, astXUnNest
  , astLetHVectorIn, astHApply, astLetFun
    -- * The expansion (e.g., into gather expressions) bottom-up pass
  , expandAst
    -- * The simplifying bottom-up pass
  , simplifyAst
    -- * The contraction (e.g., from gather expressions) bottom-up pass
  , contractAst
    -- * Substitution wrappers
  , substituteAst, substituteAstIxR, substituteAstIxS
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Control.Monad (mapAndUnzipM)
import Data.Default
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
import Foreign.C (CInt)
import GHC.Exts (IsList (..))
import GHC.TypeLits
  ( KnownNat
  , Nat
  , OrderingI (..)
  , cmpNat
  , fromSNat
  , sameNat
  , type (+)
  , type (-)
  , type (<=)
  , withKnownNat
  )
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (typeRep)

import Data.Array.Mixed.Lemmas
import Data.Array.Mixed.Permutation (DropLen, Perm (..), TakeLen, permInverse)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
  (ssxAppend, ssxFromShape, ssxReplicate, withKnownShX)
import Data.Array.Mixed.Types (Init, Last, Tail, unsafeCoerceRefl)
import Data.Array.Nested
  ( IShR
  , IxR (..)
  , IxS (..)
  , KnownShS (..)
  , KnownShX (..)
  , ListS (..)
  , MapJust
  , Product
  , Rank
  , Replicate
  , ShR (..)
  , ShS (..)
  , pattern (:$:)
  , pattern (:.$)
  , pattern (:.:)
  , pattern (::$)
  , pattern (:::)
  , pattern ZIR
  , pattern ZIS
  , pattern ZR
  , pattern ZS
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Lemmas
import Data.Array.Nested.Internal.Shape
  ( ixrAppend
  , ixrInit
  , ixrLast
  , ixrPermutePrefix
  , ixsAppend
  , ixsInit
  , ixsLast
  , ixsPermutePrefix
  , listrAppend
  , listrInit
  , listrLast
  , listsAppend
  , listsFmap
  , listsInit
  , listsLast
  , listsRank
  , shCvtSX
  , shrAppend
  , shrLast
  , shrRank
  , shrTail
  , shsAppend
  , shsHead
  , shsIndex
  , shsInit
  , shsKnownShS
  , shsLast
  , shsLength
  , shsPermute
  , shsPermutePrefix
  , shsRank
  , shsTail
  , shsTakeLen
  , withKnownShS
  )
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.Ast
  ( AstBool (AstBoolConst)
  , AstTensor (AstConcrete, AstN1, AstN1R, AstN1S, AstN2, AstN2R, AstN2S, AstSumOfList)
  )
import HordeAd.Core.Ast hiding (AstBool (..), AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.HVectorOps
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

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
  :: forall n s r. (KnownNat n, TensorKind r, AstSpan s)
  => SimplifyKnobs -> Permutation.PermR -> AstTensor AstMethodLet s (TKR2 n r)
  -> AstTensor AstMethodLet s (TKR2 n r)
{-# NOINLINE astTransposeAsGather #-}
astTransposeAsGather knobs perm v =
  let pInt = length perm
  in withSNat pInt $ \ (SNat @p) ->
    funToVarsIx pInt $ \ (!vars, !ix) ->
      let asts :: AstIxR AstMethodLet p
          asts = ixrPermutePrefix (permRInverse perm) ix
      in case cmpNat (Proxy @p) (Proxy @n) of
        EQI -> astGatherKnobsR @p @0 knobs
                 (Nested.Internal.Shape.shrPermutePrefix perm (shapeAst v)) v
                 (vars, asts)
        LTI -> astGatherKnobsR @p @(n - p) knobs
                 (Nested.Internal.Shape.shrPermutePrefix perm (shapeAst v)) v
                 (vars, asts)
        _ -> error "astTransposeAsGather: permutation longer than rank"

astTransposeAsGatherS
  :: forall perm sh s r. (TensorKind r, KnownShS sh, AstSpan s)
  => SimplifyKnobs -> Permutation.Perm perm -> AstTensor AstMethodLet s (TKS2 sh r)
  -> AstTensor AstMethodLet s (TKS2 (Permutation.PermutePrefix perm sh) r)
{-# NOINLINE astTransposeAsGatherS #-}
astTransposeAsGatherS knobs perm v =
   withKnownShS (shsDropLen perm (knownShS @sh)) $
   withKnownShS (shsTakeLen perm (knownShS @sh)) $
   withKnownShS (shsPermute perm (shsTakeLen perm (knownShS @sh))) $
   funToVarsIxS @(Permutation.Permute perm (TakeLen perm sh)) @AstMethodLet
   $ \ (!vars, !ix) ->
     -- See astGatherCase.AstTransposeS for an example with more comments.
     gcastWith (lemRankMapJust $ shsTakeLen perm (knownShS @sh)) $
     gcastWith (unsafeCoerceRefl :: Rank (TakeLen perm sh) :~: Rank perm) $
     permInverse perm $ \(invperm :: Nested.Perm invperm) proof ->
       case proof (ssxFromShape $ shCvtSX $ shsTakeLen perm (knownShS @sh)) of
         Refl ->
           gcastWith (unsafeCoerceRefl
                      :: DropLen invperm
                           (Permutation.Permute perm (TakeLen perm sh))
                         :~: '[]) $
           gcastWith (lemAppNil
                        @(Permutation.Permute invperm
                            (Permutation.Permute perm (TakeLen perm sh)))) $
           -- Seriously? This should be deduced from the above:
           gcastWith (unsafeCoerceRefl
                      :: Permutation.PermutePrefix invperm
                           (Permutation.Permute perm (TakeLen perm sh))
                         :~: Permutation.Permute invperm
                           (Permutation.Permute perm (TakeLen perm sh))) $
           -- This should follow from @proof@, if not for MapJust:
           gcastWith (unsafeCoerceRefl
                      :: Permutation.Permute invperm
                           (Permutation.Permute perm (TakeLen perm sh))
                         :~: TakeLen perm sh) $
           let asts :: AstIxS AstMethodLet (TakeLen perm sh)
               asts = ixsPermutePrefix invperm ix
           in gcastWith (unsafeCoerceRefl
                         :: TakeLen perm sh ++ DropLen perm sh :~: sh) $
              astGatherKnobsS @(Permutation.Permute perm (TakeLen perm sh))
                              @(DropLen perm sh)
                              @(TakeLen perm sh)
                              knobs v (vars, asts)

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
  :: forall p m s r. (KnownNat p, KnownNat m, TensorKind r, AstSpan s)
  => SimplifyKnobs -> IShR m -> AstTensor AstMethodLet s (TKR2 p r)
  -> AstTensor AstMethodLet s (TKR2 m r)
{-# NOINLINE astReshapeAsGather #-}
astReshapeAsGather knobs shOut v =
  funToVarsIx (sNatValue $ shrRank shOut) $ \ (!vars, !ix) ->
    let shIn = shapeAst v
        fromInt = AstConcrete FTKScalar . RepN . fromIntegral
        asts :: AstIxR AstMethodLet p
        asts = let i :: AstInt AstMethodLet
                   i = toLinearIdx @m @0 fromInt shOut ix
               in simplifyAstIxR $ fromLinearIdx fromInt shIn i
                    -- we generate these, so we simplify
    in astGatherKnobsR @m @0 knobs shOut v (vars, asts)

astReshapeAsGatherS
  :: forall sh sh2 r s. (TensorKind r, KnownShS sh, KnownShS sh2, AstSpan s)
  => SimplifyKnobs -> AstTensor AstMethodLet s (TKS2 sh r)
  -> AstTensor AstMethodLet s (TKS2 sh2 r)
{-# NOINLINE astReshapeAsGatherS #-}
astReshapeAsGatherS knobs v | Refl <- lemAppNil @sh2
                            , Refl <- lemAppNil @sh =
   funToVarsIxS @sh2 $ \ (!vars, !ix) ->
    let shIn = knownShS @sh
        shOut = knownShS @sh2
        fromInt = AstConcrete FTKScalar . RepN . fromIntegral
        asts :: AstIxS AstMethodLet sh
        asts = let i :: AstInt AstMethodLet
                   i = toLinearIdxS @sh2 @'[] fromInt shOut ix
               in simplifyAstIxS $ fromLinearIdxS fromInt shIn i
                    -- we generate these, so we simplify
    in gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh) $
       gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[]) $
       astGatherKnobsS @sh2 @'[] @sh knobs v (vars, asts)


-- * Permutation operations

normalizePermutation :: Permutation.PermR -> Permutation.PermR
normalizePermutation perm = perm
--  map fst $ dropWhileEnd (uncurry (==)) $ zip perm [0 ..]
-- TODO: port to shaped permutations and then re-enable and replace the below
normalizePermutationHack :: Permutation.PermR -> Permutation.PermR
normalizePermutationHack perm =
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
  Ast.AstPair t1 t2 -> astPair (astNonIndexStep t1) (astNonIndexStep t2)
  Ast.AstProject1 u -> astProject1 u
  Ast.AstProject2 u -> astProject2 u
--  Ast.AstApply v ll -> astHApply v ll
  Ast.AstVar{} -> t
  Ast.AstPrimalPart v -> astPrimalPart v  -- has to be done sooner or later
  Ast.AstDualPart v -> astDualPart v
  Ast.AstFromPrimal{} -> t
  Ast.AstD{} -> t
  Ast.AstCond a b c -> astCond a b c
  Ast.AstFromVector snat l -> astFromVector snat l
  Ast.AstSum snat stk v -> astSum snat stk v
  Ast.AstReplicate snat stk v -> astReplicate snat stk v
  Ast.AstBuild1{} -> t
  Ast.AstLet var u v -> astLet var u v
  AstConcrete{} -> t
--  Ast.AstMapAccumRDer @accShs @bShs @eShs k accShs bShs eShs f df rf acc0 es
--  Ast.AstMapAccumLDer @accShs @bShs @eShs k accShs bShs eShs f df rf acc0 es

  AstSumOfList stk args ->
    case isTensorInt t of
      Just Refl -> foldr1 contractAstPlusOp args
      _ -> astSumOfList stk args

  AstN1 opCode u ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp1 opCode u
      _ -> t
  AstN2 opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp2 opCode u v
      _ -> t
  Ast.AstR1{} -> t
  Ast.AstR2{} -> t
  Ast.AstI2 opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstIntegralOp2 opCode u v
      _ -> t
  Ast.AstFloor{} -> t
  Ast.AstFromIntegral v -> astFromIntegral v
  Ast.AstCast v -> astCast v

  AstN1R{} -> t
  AstN2R{} -> t
  Ast.AstR1R{} -> t
  Ast.AstR2R{} -> t
  Ast.AstI2R{} -> t
  Ast.AstFloorR{} -> t
  Ast.AstFromIntegralR v -> astFromIntegralR v
  Ast.AstCastR v -> astCastR v
  Ast.AstMinIndexR{} -> t
  Ast.AstMaxIndexR{} -> t
  Ast.AstIotaR{} -> t
  Ast.AstIndex{} -> t  -- was supposed to be *non*-index
  Ast.AstScatter sh v (vars, ix) -> astScatter sh v (vars, ix)
  Ast.AstAppend x y -> astAppend x y
  Ast.AstSlice i k v -> astSlice i k v
  Ast.AstReverse v -> astReverse v
  Ast.AstTranspose perm v -> astTranspose perm v
  Ast.AstReshape sh v -> astReshape sh v
  Ast.AstGather _ v0 (ZR, ix) -> Ast.AstIndex v0 ix
  Ast.AstGather sh v0 (_, ZIR) -> astReplicateN sh v0
  Ast.AstGather{} -> t  -- this is "index" enough
  Ast.AstZipR _ -> t
  Ast.AstUnzipR _ -> t

  Ast.AstFromScalar u -> astFromScalar $ astNonIndexStep u
  Ast.AstToScalar u -> Ast.AstToScalar $ astNonIndexStep u
  AstN1S{} -> t
  AstN2S{} -> t
  Ast.AstR1S{} -> t
  Ast.AstR2S{} -> t
  Ast.AstI2S{} -> t
  Ast.AstFloorS{} -> t
  Ast.AstFromIntegralS v -> astFromIntegralS v
  Ast.AstCastS v -> astCastS v
  Ast.AstMinIndexS{} -> t
  Ast.AstMaxIndexS{} -> t
  Ast.AstIotaS -> t
  Ast.AstIndexS{} -> t  -- was supposed to be *non*-index
  Ast.AstScatterS @shm @shn @shp v (vars, ix) ->
    astScatterS @shm @shn @shp v (vars, ix)
  Ast.AstAppendS x y -> astAppendS x y
  Ast.AstSliceS @i @k v -> astSliceS @i @k v
  Ast.AstReverseS v -> astReverseS v
  Ast.AstTransposeS perm v -> astTransposeS perm v
  Ast.AstReshapeS v -> astReshapeS v
  Ast.AstGatherS v0 (ZS, ix) ->
    Ast.AstIndexS v0 ix
  Ast.AstGatherS @shm @shn @shp v0 (_ , ZIS) ->
    astReplicateNS @shm @(shp ++ shn) v0
  Ast.AstGatherS{} -> t  -- this is "index" enough
  Ast.AstZipS _ -> t
  Ast.AstUnzipS _ -> t

  Ast.AstRFromS v -> astRFromS v
  Ast.AstSFromR v -> astSFromR v
  Ast.AstSFromX v -> astSFromX v
  Ast.AstXFromS v -> astXFromS v

  Ast.AstXNestR v -> astXNestR v
  Ast.AstXNestS v -> astXNestS v
  Ast.AstXNest v -> astXNest v
  Ast.AstXUnNestR v -> astXUnNestR v
  Ast.AstXUnNestS v -> astXUnNestS v
  Ast.AstXUnNest v -> astXUnNest v

  -- These should not appear here unless via wacky tests.
  Ast.AstReplicate0NR{} -> t
  Ast.AstSum0R{} -> t
  Ast.AstDot0R{} -> t
  Ast.AstDot1InR{} -> t
  Ast.AstMatvecmulR{} -> t
  Ast.AstMatmul2R{} -> t
  Ast.AstReplicate0NS{} -> t
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatvecmulS{} -> t
  Ast.AstMatmul2S{} -> t

--  Ast.AstMkHVector l -> Ast.AstMkHVector $ V.map simplifyAstDynamic l
  Ast.AstProjectR l p -> astProjectR l p
  Ast.AstLetHVectorIn vars u v -> astLetHVectorIn vars u v
  Ast.AstProjectS l p -> astProjectS l p

  _ -> t  -- TODO

astIndexR
  :: forall m n s r.
     (KnownNat m, KnownNat n, TensorKind r, AstSpan s)
  => AstTensor AstMethodLet s (TKR2 (m + n) r) -> AstIxR AstMethodLet m
  -> AstTensor AstMethodLet s (TKR2 n r)
astIndexR = astIndexKnobsR defaultKnobs

astIndexStep
  :: forall m n s r.
     (KnownNat m, KnownNat n, TensorKind r, AstSpan s)
  => AstTensor AstMethodLet s (TKR2 (m + n) r) -> AstIxR AstMethodLet m
  -> AstTensor AstMethodLet s (TKR2 n r)
astIndexStep v ix = astIndexKnobsR (defaultKnobs {knobStepOnly = True})
                                   (astNonIndexStep v)
                                   (simplifyAstIxR ix)

astIndexS
  :: forall shm shn s r.
     (KnownShS shm, KnownShS shn, TensorKind r, AstSpan s)
  => AstTensor AstMethodLet s (TKS2 (shm ++ shn) r) -> AstIxS AstMethodLet shm
  -> AstTensor AstMethodLet s (TKS2 shn r)
astIndexS = astIndexKnobsS defaultKnobs

astIndexStepS
  :: forall shm shn s r.
     (KnownShS shm, KnownShS shn, TensorKind r, AstSpan s)
  => AstTensor AstMethodLet s (TKS2 (shm ++ shn) r) -> AstIxS AstMethodLet shm
  -> AstTensor AstMethodLet s (TKS2 shn r)
astIndexStepS v ix =
  withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
  astIndexKnobsS (defaultKnobs {knobStepOnly = True})
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
     (KnownNat m, KnownNat n, TensorKind r, AstSpan s)
  => SimplifyKnobs
  -> AstTensor AstMethodLet s (TKR2 (m + n) r)
  -> AstIxR AstMethodLet m
  -> AstTensor AstMethodLet s (TKR2 n r)
astIndexKnobsR knobs (Ast.AstIndex v ix) ZIR =
  astIndexKnobsR knobs v ix  -- no non-indexing constructor yet revealed
astIndexKnobsR _ v0 ZIR = v0
astIndexKnobsR knobs v0 ix@(i1 :.: (rest1 :: AstIxR AstMethodLet m1)) =
 let astIndexRec, astIndex
       :: forall m' n' s'. (KnownNat m', KnownNat n', AstSpan s')
       => AstTensor AstMethodLet s' (TKR2 (m' + n') r) -> AstIxR AstMethodLet m'
       -> AstTensor AstMethodLet s' (TKR2 n' r)
     astIndexRec v2 ZIR = v2
     astIndexRec v2 ix2 = if knobStepOnly knobs
                          then Ast.AstIndex v2 ix2
                          else astIndexKnobsR knobs v2 ix2
     astIndex v2 ix2 = if knobStepOnly knobs
                       then astIndexKnobsR knobs
                                           (astNonIndexStep v2)
                                           (simplifyAstIxR ix2)
                       else astIndexKnobsR knobs v2 ix2
     astGather
       :: forall m' n' p'.
          (KnownNat m', KnownNat p', KnownNat n')
       => IShR (m' + n') -> AstTensor AstMethodLet s (TKR2 (p' + n') r)
       -> (AstVarList m', AstIxR AstMethodLet p')
       -> AstTensor AstMethodLet s (TKR2 (m' + n') r)
     astGather sh2 v2 (vars2, ix2) =
       if knobStepOnly knobs
       then astGatherKnobsR knobs
                            sh2 (astNonIndexStep v2)
                            (vars2, simplifyAstIxR ix2)
       else astGatherKnobsR knobs sh2 v2 (vars2, ix2)
 in case v0 of
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
  Ast.AstSum snat _ v ->  -- almost neutral; transposition is likely to fuse away
    let perm3 = backpermCycle $ valueOf @m + 1
    in astSum snat stensorKind $ astIndex (astTranspose perm3 v) ix
  Ast.AstReplicate snat STKR{} v | AstConcrete _ (RepN it) <- i1 ->
    let i = fromIntegral it
    in if 0 <= i && i < sNatValue snat
       then astIndex v rest1
       else case ftkAst v of
         FTKR sh x ->
           let ftk = FTKR (dropShape sh) x
           in fromPrimal $ AstConcrete ftk (constantTarget def ftk)
{- TODO: this generalization of the above case slows down test 3nestedSumBuild1
   orders of magnitude
  Ast.AstReplicate k v ->
    let len = AstConcrete $ Nested.rscalar $ fromIntegral k
        zero = astReplicate0N (dropShape $ shapeAst v) 0
    in case simplifyAstBool $ Ast.AstB2 AndOp (Ast.AstRel LeqOp 0 i1)
                                              (Ast.AstRel LsOp i1 len) of
      AstBoolConst b -> if b then astIndex v rest1 else zero
      bExpr -> astCond bExpr (astIndex v rest1) zero -}
  Ast.AstReplicate _ STKR{} v -> astIndex v rest1
  Ast.AstBuild1 @y2 _snat (var2, v) | STKR{} <- stensorKind @y2 ->
    astIndex (astLet var2 i1 v) rest1
  Ast.AstLet var u v -> astLet var u (astIndexRec v ix)

  AstSumOfList _ args ->
    shareIx ix $ \ !ix2 ->
      astSumOfList stensorKind (map (`astIndexRec` ix2) args)

  Ast.AstMinIndexR v -> Ast.AstMinIndexR $ astIndexKnobsR knobs v ix
  Ast.AstMaxIndexR v -> Ast.AstMaxIndexR $ astIndexKnobsR knobs v ix
  Ast.AstFloorR v -> Ast.AstFloorR $ astIndexKnobsR knobs v ix
  Ast.AstIotaR{}
   | AstConcrete _ (RepN i) <- i1 -> case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> astFromIntegralR
                 $ AstConcrete (FTKR ZSR FTKScalar) $ RepN $ Nested.rscalar i
    _ -> error "astIndexKnobsR: rank not 0"
  Ast.AstIotaR{} -> Ast.AstIndex v0 ix
  AstN1R opCode u -> AstN1R opCode (astIndexRec u ix)
  AstN2R opCode u v ->
    shareIx ix $ \ !ix2 -> AstN2R opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstR1R opCode u -> Ast.AstR1R opCode (astIndexRec u ix)
  Ast.AstR2R opCode u v ->
    shareIx ix
    $ \ !ix2 -> Ast.AstR2R opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstI2R opCode u v ->
    shareIx ix
    $ \ !ix2 -> Ast.AstI2R opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstIndex v ix2 ->
    astIndex v (ix2 `ixrAppend` ix)
  Ast.AstScatter @_ @n7 (_ :$: sh)
                 v (vars, AstIntVar var5 :.: (ix2 :: AstIxR AstMethodLet p71))
    | AstIntVar var6 <- i1, var6 == var5 ->
        gcastWith (unsafeCoerceRefl :: m1 + n :~: p71 + n7) $
        astIndex (astScatter sh v (vars, ix2)) rest1
  Ast.AstScatter @_ @n7 (_ :$: sh)
                 v (vars, AstConcrete _ i5 :.: (ix2 :: AstIxR AstMethodLet p71))
    | AstConcrete _ i6 <- i1
    , STKScalar{} <- stensorKind @r ->
        gcastWith (unsafeCoerceRefl :: m1 + n :~: p71 + n7) $
        if i6 == i5
        then astIndex (astScatter sh v (vars, ix2)) rest1
        else astReplicate0N (dropShape @m1 sh) def
  -- AstScatter sh v (vars2, ZIR) ->
  --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZIR)
  Ast.AstScatter{} ->  -- normal form
    Ast.AstIndex v0 ix
  Ast.AstFromVector @y2 snat l | AstConcrete _ (RepN it) <- i1
                               , STKR{} <- stensorKind @y2 ->
    let i = fromIntegral it
    in if 0 <= i && i < sNatValue snat
       then astIndex (l V.! i) rest1
       else case ftkAst v0 of
         FTKR sh x ->
           let ftk = FTKR (dropShape sh) x
           in fromPrimal $ AstConcrete ftk (constantTarget def ftk)
  Ast.AstFromVector{} | ZIR <- rest1 ->  -- normal form
    Ast.AstIndex v0 ix
  Ast.AstFromVector @y2 snat l | STKR{} <- stensorKind @y2 ->
    shareIx rest1 $ \ !ix2 ->
      Ast.AstIndex (astFromVector snat $ V.map (`astIndexRec` ix2) l)
                   (i1 :.: ZIR)
  Ast.AstAppend u v ->
    let ulen = AstConcrete FTKScalar $ RepN $ fromIntegral $ lengthAst u
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
    astIndex v (ixrPermutePrefix (permRInverse perm) ix)
  Ast.AstTranspose perm v -> astIndex (astTransposeAsGather knobs perm v) ix
  Ast.AstReshape sh v -> astIndex (astReshapeAsGather knobs sh v) ix
  Ast.AstGather _sh v (ZR, ix2) -> astIndex v (ix2 `ixrAppend` ix)
  Ast.AstGather @_ @n7 (_ :$: sh') v (var2 ::: (vars :: AstVarList m71), ix2) ->
    let w :: AstTensor AstMethodLet s (TKR2 (m1 + n) r)
        w = gcastWith (unsafeCoerceRefl :: m1 + n :~: m71 + n7) $
            astGather sh' v (vars, ix2)
    in astLet var2 i1 $ astIndex w rest1
  Ast.AstGather{} ->
    error "astIndex: AstGather: impossible pattern needlessly required"
  Ast.AstCastR t -> astCastR $ astIndexKnobsR knobs t ix
  Ast.AstFromIntegralR v -> astFromIntegralR $ astIndexKnobsR knobs v ix
  AstConcrete (FTKR _ x) t ->
    let unConst :: AstInt AstMethodLet -> Maybe [IntOf RepN]
                -> Maybe [IntOf RepN]
        unConst (AstConcrete _ i) (Just l) = Just $ i : l
        unConst _ _ = Nothing
    in case foldr unConst (Just []) ix of
      Just ixInt ->
        let u = rindex t (fromList ixInt)
        in AstConcrete (FTKR (rshape u) x) u
          -- TODO: we'd need mapM for Index to keep this rank-typed
      Nothing -> Ast.AstIndex v0 ix
  Ast.AstProjectR{} -> Ast.AstIndex v0 ix
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars l (astIndexRec v ix)
  Ast.AstZipR _ -> Ast.AstIndex v0 ix

  Ast.AstRFromS @sh t ->
    withKnownShS (takeShS @m (knownShS @sh)) $
    withKnownShS (dropShS @m (knownShS @sh)) $
    gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
    gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
    gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
    astRFromS $ astIndexKnobsS @(Take m sh) @(Drop m sh)
                               knobs t (ixrToIxs ix)

  Ast.AstApply{} -> Ast.AstIndex v0 ix

  -- The below should not appear here unless via wacky tests.
  Ast.AstReplicate0NR{} -> Ast.AstIndex v0 ix
  Ast.AstSum0R{} -> Ast.AstIndex v0 ix
  Ast.AstDot0R{} -> Ast.AstIndex v0 ix
  Ast.AstDot1InR{} -> Ast.AstIndex v0 ix
  Ast.AstMatvecmulR{} -> Ast.AstIndex v0 ix
  Ast.AstMatmul2R{} -> Ast.AstIndex v0 ix

astIndexKnobsS
  :: forall shm shn s r.
     (KnownShS shm, KnownShS shn, TensorKind r, AstSpan s)
  => SimplifyKnobs
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
  -> AstIxS AstMethodLet shm
  -> AstTensor AstMethodLet s (TKS2 shn r)
astIndexKnobsS knobs (Ast.AstIndexS v ix) ZIS =
  astIndexKnobsS knobs v ix  -- no non-indexing constructor yet revealed
astIndexKnobsS _ v0 ZIS = v0
astIndexKnobsS knobs v0 ix@((:.$) @in1 @shm1 i1 rest1)
               | Dict <- sixKnown rest1 =
 withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
 let astIndexRec, astIndex
       :: forall shm' shn' s'.
          (KnownShS shm', KnownShS shn', AstSpan s')
       => AstTensor AstMethodLet s' (TKS2 (shm' ++ shn') r)
       -> AstIxS AstMethodLet shm'
       -> AstTensor AstMethodLet s' (TKS2 shn' r)
     astIndexRec v2 ZIS = v2
     astIndexRec v2 ix2 =
       withKnownShS (knownShS @shm' `shsAppend` knownShS @shn') $
       if knobStepOnly knobs
       then Ast.AstIndexS v2 ix2
       else astIndexKnobsS knobs v2 ix2
     astIndex v2 ix2 =
       withKnownShS (knownShS @shm' `shsAppend` knownShS @shn') $
       if knobStepOnly knobs
       then astIndexKnobsS knobs (astNonIndexStep v2) (simplifyAstIxS ix2)
       else astIndexKnobsS knobs v2 ix2
     astGather
       :: forall shm' shn' shp'.
          (KnownShS shm', KnownShS shn', KnownShS shp')
       => AstTensor AstMethodLet s (TKS2 (shp' ++ shn') r)
       -> (AstVarListS shm', AstIxS AstMethodLet shp')
       -> AstTensor AstMethodLet s (TKS2 (shm' ++ shn') r)
     astGather v2 (vars2, ix2) =
       withKnownShS (knownShS @shp' `shsAppend` knownShS @shn') $
       if knobStepOnly knobs
       then astGatherKnobsS @shm' @shn' @shp'
                            knobs
                            (astNonIndexStep v2)
                            (vars2, simplifyAstIxS ix2)
       else astGatherKnobsS @shm' @shn' @shp' knobs v2 (vars2, ix2)
 in case v0 of
  Ast.AstProject1{} -> Ast.AstIndexS v0 ix
  Ast.AstProject2{} -> Ast.AstIndexS v0 ix
  Ast.AstApply{} -> Ast.AstIndexS v0 ix
  Ast.AstVar{} -> Ast.AstIndexS v0 ix
  Ast.AstPrimalPart{} -> Ast.AstIndexS v0 ix  -- must be a NF
  Ast.AstDualPart{} -> Ast.AstIndexS v0 ix
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astIndex v ix
  Ast.AstD u u' ->
    shareIx ix $ \ !ix2 -> Ast.AstD (astIndexRec u ix2) (astIndexRec u' ix2)
  Ast.AstCond b v w ->
    shareIx ix $ \ !ix2 -> astCond b (astIndexRec v ix2) (astIndexRec w ix2)
  Ast.AstFromVector @y2 snat l | AstConcrete _ (RepN it) <- i1
                               , STKS{} <- stensorKind @y2 ->
    let i = fromIntegral it
    in if 0 <= i && i < sNatValue snat
       then astIndex (l V.! i) rest1
       else case ftkAst v0 of
         FTKS _ x ->
           let ftk = FTKS knownShS x
           in fromPrimal $ AstConcrete ftk (constantTarget def ftk)
  Ast.AstFromVector{} | ZIS <- rest1 ->  -- normal form, STKScalar case included
    Ast.AstIndexS v0 ix
  Ast.AstFromVector @y2 snat l | STKS{} <- stensorKind @y2 ->
    shareIx rest1 $ \ !ix2 ->
      Ast.AstIndexS @'[in1] @shn (astFromVector snat $ V.map (`astIndexRec` ix2) l)
                    (i1 :.$ ZIS)
  Ast.AstFromVector{} -> error "astIndexKnobsS: impossible case"
  Ast.AstSum snat@(SNat @n1) _ v ->
    let perm3 = backpermCycle $ shsLength (knownShS @shm) + 1
    in Permutation.permFromList perm3 $ \(perm :: Permutation.Perm perm3P) ->
         gcastWith (unsafeCoerceRefl
                    :: Compare (Rank perm3P) (Rank (n1 : shm ++ shn))
                       :~: LT) $
         gcastWith (unsafeCoerceRefl
                    :: Permutation.PermutePrefix perm3P (n1 : (shm ++ shn))
                       :~: shm ++ (n1 : shn)) $
         trustMeThisIsAPermutation @perm3P $
         astSum snat stensorKind
         $ astIndex @shm @(n1 : shn)
                    (astTransposeS @perm3P @(n1 : shm ++ shn) perm v)
                    ix
  Ast.AstReplicate snat (STKS sh _) v | AstConcrete _ (RepN it) <- i1 ->
      withKnownShS sh $
      let i = fromIntegral it
      in if 0 <= i && i < sNatValue snat
         then astIndex v rest1
         else case ftkAst v of
           FTKS _ x ->
             let ftk = FTKS knownShS x
             in fromPrimal $ AstConcrete ftk (constantTarget def ftk)
  Ast.AstReplicate _ (STKS sh _) v -> withKnownShS sh $ astIndex v rest1
  Ast.AstReplicate _ STKScalar{} v | ZIS <- rest1 -> astFromScalar v
  Ast.AstBuild1 @y2 _snat (var2, v) -> case stensorKind @y2 of
    STKScalar{} | ZIS <- rest1 -> astFromScalar $ astLet var2 i1 v
    STKS sh _ ->
      withKnownShS sh $
      withKnownShS (knownShS @shm1 `shsAppend` knownShS @shn) $
      astIndex (astLet var2 i1 v) rest1
  Ast.AstLet var u v -> astLet var u (astIndexRec v ix)
  AstConcrete (FTKS _ x) t ->
    let unConst :: AstInt AstMethodLet -> Maybe [IntOf RepN]
                -> Maybe [IntOf RepN]
        unConst (AstConcrete _ i) (Just l) = Just $ i : l
        unConst _ _ = Nothing
    in case foldr unConst (Just []) ix of
      Just ixInt -> AstConcrete (FTKS knownShS x)
                    $ sindex @_ @_ @shm t (fromList ixInt)
        -- TODO: we'd need mapM for Index to keep this rank-typed
      Nothing -> Ast.AstIndexS v0 ix

  AstSumOfList _ args ->
    shareIx ix $ \ !ix2 ->
      astSumOfList stensorKind (map (`astIndexRec` ix2) args)

  AstN1S opCode u -> AstN1S opCode (astIndexRec u ix)
  AstN2S opCode u v ->
    shareIx ix $ \ !ix2 -> AstN2S opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astIndexRec u ix)
  Ast.AstR2S opCode u v ->
    shareIx ix
    $ \ !ix2 -> Ast.AstR2S opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstI2S opCode u v ->
    shareIx ix
    $ \ !ix2 -> Ast.AstI2S opCode (astIndexRec u ix2) (astIndexRec v ix2)
  Ast.AstFloorS v -> Ast.AstFloorS $ astIndexKnobsS knobs v ix
  Ast.AstFromIntegralS v -> astFromIntegralS $ astIndexKnobsS knobs v ix
  Ast.AstCastS t -> astCastS $ astIndexKnobsS knobs t ix
  Ast.AstMinIndexS @shz @n1 v -> case shsLast (SNat @n1 :$$ knownShS @shz) of
    nl@SNat ->
      let shnl = knownShS @shn `shsAppend` (nl :$$ ZSS)
      in withKnownNat (shsIndex Proxy Proxy (SNat @0) shnl) $
         withKnownShS shnl $
         withKnownShS (dropShS @1 shnl) $
           -- TODO: (shsTail shnl) would be more precise, but ++ is stuck at shn
           -- and can't produce ': at this point
         gcastWith (unsafeCoerceRefl
                    :: Permutation.Index 0 (shn ++ '[Last (n1 : shz)])
                       ': Drop 1 (shn ++ '[Last (n1 : shz)])
                       :~: shn ++ '[Last (n1 : shz)]) $
         gcastWith (unsafeCoerceRefl
                    :: Init (shn ++ '[Last (n1 : shz)]) :~: shn) $
         gcastWith (unsafeCoerceRefl
                    :: shm ++ (shn ++ '[Last (n1 : shz)]) :~: n1 ': shz) $
         Ast.AstMinIndexS @(Drop 1 (shn ++ '[Last (n1 : shz)]))
                          @(Permutation.Index 0 (shn ++ '[Last (n1 : shz)]))
         $ astIndexKnobsS @shm @(shn ++ '[Last (n1 : shz)]) knobs v ix
  Ast.AstMaxIndexS @shz @n1 v -> case shsLast (SNat @n1 :$$ knownShS @shz) of
    nl@SNat ->
      let shnl = knownShS @shn `shsAppend` (nl :$$ ZSS)
      in withKnownNat (shsIndex Proxy Proxy (SNat @0) shnl) $
         withKnownShS shnl $
         withKnownShS (dropShS @1 shnl) $
           -- TODO: (shsTail shnl) would be more precise, but ++ is stuck at shn
           -- and can't produce ': at this point
         gcastWith (unsafeCoerceRefl
                    :: Permutation.Index 0 (shn ++ '[Last (n1 : shz)])
                       ': Drop 1 (shn ++ '[Last (n1 : shz)])
                       :~: shn ++ '[Last (n1 : shz)]) $
         gcastWith (unsafeCoerceRefl
                    :: Init (shn ++ '[Last (n1 : shz)]) :~: shn) $
         gcastWith (unsafeCoerceRefl
                    :: shm ++ (shn ++ '[Last (n1 : shz)]) :~: n1 ': shz) $
         Ast.AstMaxIndexS @(Drop 1 (shn ++ '[Last (n1 : shz)]))
                          @(Permutation.Index 0 (shn ++ '[Last (n1 : shz)]))
         $ astIndexKnobsS @shm @(shn ++ '[Last (n1 : shz)]) knobs v ix
  Ast.AstIotaS | AstConcrete _ (RepN i) <- i1 -> case sameShape @shn @'[] of
    Just Refl -> astFromIntegralS
                 $ AstConcrete (FTKS ZSS FTKScalar) $ RepN $ Nested.sscalar i
    _ -> error "astIndexKnobsS: shape not []"
-- TODO:  AstIndexS AstIotaS (i :.$ ZIS) ->
--    sfromIntegral . sfromPrimal . sfromR . rfromScalar $ interpretAstPrimal env i
  Ast.AstIotaS -> Ast.AstIndexS v0 ix
  Ast.AstIndexS v (ix2 :: AstIxS AstMethodLet sh4)
   | Refl <- lemAppAssoc (Proxy @sh4) (Proxy @shm) (Proxy @shn) ->
    withKnownShS (knownShS @sh4 `shsAppend` knownShS @shm) $
    astIndexS v (ix2 `ixsAppend` ix)
  Ast.AstScatterS @shm7 @shn7 @shp7 v (vars, AstIntVar var5 :.$ ix2)
    | AstIntVar var6 <- i1, var6 == var5, Dict <- sixKnown ix2 ->
        astIndex (astScatterS @shm7 @shn7 @(Tail shp7) v (vars, ix2)) rest1
  Ast.AstScatterS @shm7 @shn7 @shp7 v (vars, AstConcrete _ i5 :.$ ix2)
    | AstConcrete _ i6 <- i1, Dict <- sixKnown ix2
    , STKScalar{} <- stensorKind @r ->
        if i6 == i5
        then astIndex (astScatterS @shm7 @shn7 @(Tail shp7) v (vars, ix2)) rest1
        else astReplicate0NS @shn 0
  -- AstScatter sh v (vars2, ZIR) ->
  --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZIR)
  Ast.AstScatterS{} ->  -- normal form
    Ast.AstIndexS v0 ix
  Ast.AstAppendS @m u v ->
    let ulen = AstConcrete FTKScalar $ RepN $ valueOf @m
        ix1 = i1 :.$ rest1
        ix2 = simplifyAstInt (AstN2 MinusOp i1 ulen) :.$ rest1
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
    | gcompare (shsRank (knownShS @shm)) (Permutation.permRank perm) == GLT ->
        astIndex (astTransposeAsGatherS @perm knobs perm v) ix
  Ast.AstTransposeS @perm @sh2 perm v ->
    withKnownShS (shsPermutePrefix perm (knownShS @shm)) $
    let ix2 :: AstIxS AstMethodLet (Permutation.PermutePrefix perm shm)
        ix2 = ixsPermutePrefix perm ix
    in gcastWith (unsafeCoerceRefl
                  :: sh2 :~: Permutation.PermutePrefix perm shm ++ shn) $
       astIndex @(Permutation.PermutePrefix perm shm) v ix2
  Ast.AstReshapeS v -> astIndex (astReshapeAsGatherS knobs v) ix
  Ast.AstGatherS @_ @_ @shp' v (ZS, ix2) ->
    gcastWith (unsafeCoerceRefl
              :: shp' ++ (in1 ': shm1) ++ shn :~: shp' ++ (in1 ': shm1 ++ shn)) $
    withKnownShS (knownShS @shp' `shsAppend` knownShS @shm) $
    astIndex @(shp' ++ shm) @shn v (ix2 `ixsAppend` ix)
  Ast.AstGatherS @_ @shn' @shp' v ((::$) @_ @shm71 (Const var2) vars, ix2)
                 | Dict <- slistKnown vars ->
    gcastWith (unsafeCoerceRefl :: shm71 ++ shn' :~: shm1 ++ shn) $
      let w :: AstTensor AstMethodLet s (TKS2 (shm1 ++ shn) r)
          w = astGather @shm71 @shn' @shp' v (vars, ix2)
      in astLet var2 i1 $ astIndexS @shm1 @shn w rest1
  Ast.AstZipS _ -> Ast.AstIndexS v0 ix

  -- These conversions need to stay down.
  Ast.AstSFromR{} -> Ast.AstIndexS v0 ix
  Ast.AstSFromX{} -> Ast.AstIndexS v0 ix

  -- These should not appear here unless via wacky tests.
  Ast.AstReplicate0NS{} -> Ast.AstIndexS v0 ix
-- impossible: Ast.AstSum0S{} -> Ast.AstIndexS v0 ix
-- impossible: Ast.AstDot0S{} -> Ast.AstIndexS v0 ix
  Ast.AstDot1InS{} -> Ast.AstIndexS v0 ix
  Ast.AstMatvecmulS{} -> Ast.AstIndexS v0 ix
  Ast.AstMatmul2S{} -> Ast.AstIndexS v0 ix

  Ast.AstProjectS{} -> Ast.AstIndexS v0 ix
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars l (astIndexRec v ix)

-- TODO: compared to tletIx, it adds many lets, not one, but does not
-- create other (and non-simplified!) big terms and also uses astIsSmall,
-- so it's probably more efficient. Use this instead of tletIx
-- or design something even better.
shareIx :: (TensorKind y, IsList indexType, Item indexType ~ AstInt AstMethodLet)
        => indexType
        -> (indexType -> AstTensor AstMethodLet s y)
        -> AstTensor AstMethodLet s y
{-# NOINLINE shareIx #-}
shareIx ix f = unsafePerformIO $ do
  let shareI :: AstInt AstMethodLet
             -> IO (Maybe (IntVarName, AstInt AstMethodLet), AstInt AstMethodLet)
      shareI i | astIsSmall True i = return (Nothing, i)
      shareI i = funToAstIntVarIO $ \ (!varFresh, !astVarFresh) ->
                   (Just (varFresh, i), astVarFresh)
  (bindings, ix2) <- mapAndUnzipM shareI (toList ix)
  return $! foldr (uncurry Ast.AstLet) (f $ fromList ix2)
                                       (catMaybes bindings)

astGatherR
  :: forall m n p s r.
     (KnownNat m, KnownNat p, KnownNat n, TensorKind r, AstSpan s)
  => IShR (m + n) -> AstTensor AstMethodLet s (TKR2 (p + n) r) -> (AstVarList m, AstIxR AstMethodLet p)
  -> AstTensor AstMethodLet s (TKR2 (m + n) r)
astGatherR = astGatherKnobsR defaultKnobs

astGatherS
  :: forall shm shn shp r s.
     (KnownShS shm, KnownShS shn, KnownShS shp, TensorKind r, AstSpan s)
  => AstTensor AstMethodLet s (TKS2 (shp ++ shn) r)
  -> (AstVarListS shm, AstIxS AstMethodLet shp)
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
astGatherS = astGatherKnobsS @shm @shn @shp defaultKnobs

astGatherStep
  :: forall m n p s r.
     (KnownNat m, KnownNat p, KnownNat n, TensorKind r, AstSpan s)
  => IShR (m + n) -> AstTensor AstMethodLet s (TKR2 (p + n) r) -> (AstVarList m, AstIxR AstMethodLet p)
  -> AstTensor AstMethodLet s (TKR2 (m + n) r)
astGatherStep sh v (vars, ix) =
  astGatherKnobsR (defaultKnobs {knobStepOnly = True})
                  sh (astNonIndexStep v)
                  (vars, simplifyAstIxR ix)

astGatherStepS
  :: forall shm shn shp r s.
     (KnownShS shm, KnownShS shn, KnownShS shp, TensorKind r, AstSpan s)
  => AstTensor AstMethodLet s (TKS2 (shp ++ shn) r)
  -> (AstVarListS shm, AstIxS AstMethodLet shp)
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
-- TODO: this probably needs an extra condition similar to kN == vkN below
--astGatherStepS v (AstVarName varId ::$ ZSS, AstIntVarS varId2 :.$ ZIS)
--  | varId == varId2 = ...
astGatherStepS v (vars, ix) =
  withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
  astGatherKnobsS @shm @shn @shp
                  (defaultKnobs {knobStepOnly = True})
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
     (KnownNat m, KnownNat p, KnownNat n, TensorKind r, AstSpan s)
  => SimplifyKnobs -> IShR (m + n) -> AstTensor AstMethodLet s (TKR2 (p + n) r)
  -> (AstVarList m, AstIxR AstMethodLet p)
  -> AstTensor AstMethodLet s (TKR2 (m + n) r)
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
           else case shrRank sh' of
             SNat -> withSNat k $ \snat ->
               astReplicate snat stensorKind
                            (astGatherKnobsR knobs sh' v0 (vars, ix0))
       where
        restN = ixrInit ix0
        iN = ixrLast ix0
        varsN = listrInit vars0
        varN = listrLast vars0
    _ ->
      error "astGather: impossible pattern needlessly required"
 where
  astIndex :: forall m' n' s'. (KnownNat m', KnownNat n', AstSpan s')
           => AstTensor AstMethodLet s' (TKR2 (m' + n') r) -> AstIxR AstMethodLet m'
           -> AstTensor AstMethodLet s' (TKR2 n' r)
  astIndex v2 ix2 = if knobStepOnly knobs
                    then astIndexKnobsR knobs
                                        (astNonIndexStep v2)
                                        (simplifyAstIxR ix2)
                    else astIndexKnobsR knobs v2 ix2
  astGatherRec, astGather
    :: forall m' n' p' s' r'.
       (KnownNat m', KnownNat p', KnownNat n', AstSpan s', TensorKind r')
    => IShR (m' + n') -> AstTensor AstMethodLet s' (TKR2 (p' + n') r')
    -> (AstVarList m', AstIxR AstMethodLet p')
    -> AstTensor AstMethodLet s' (TKR2 (m' + n') r')
  astGatherRec sh2 v2 (vars2, ix2) =
    if knobStepOnly knobs
    then Ast.AstGather sh2 v2 (vars2, ix2)
    else astGatherKnobsR knobs sh2 v2 (vars2, ix2)
  astGather sh2 v2 (vars2, ix2) =
    if knobStepOnly knobs
    then astGatherKnobsR knobs
                         sh2 (astNonIndexStep v2)
                         (vars2, simplifyAstIxR ix2)
    else astGatherKnobsR knobs sh2 v2 (vars2, ix2)
  -- Note that v4 is in weak head normal form and so can't one-step reduce
  -- and so we don't have to reduce it to expose any top redexes.
  astGatherCase
    :: forall m' n' p'.
       (KnownNat m', KnownNat p', KnownNat n')
    => IShR (m' + n') -> AstTensor AstMethodLet s (TKR2 (p' + n') r)
    -> (AstVarList m', AstIxR AstMethodLet p')
    -> AstTensor AstMethodLet s (TKR2 (m' + n') r)
  astGatherCase sh4 v4 (_, ZIR) = astReplicateN sh4 v4  -- not really possible
  astGatherCase sh4 v4 ( vars4
                       , ix4@((:.:) @p1' i4 rest4) ) = case v4 of
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
      funToVarsIx (valueOf @m') $ \ (!varsFresh, IxR !ixFresh) ->
        -- This subst doesn't currently break sharing, because it's a rename.
        let subst i =
              foldr (\(i2, var2) v2 ->
                       substituteAst i2 var2 v2)
                    i
                    (zipSized ixFresh vars4)
            ix5 = fmap subst ix4
        in Ast.AstD (astGatherRec sh4 u (vars4, ix4))
                    (astGatherRec sh4 u' (varsFresh, ix5))
    Ast.AstCond b v w -> astCond b (astGather sh4 v (vars4, ix4))
                                   (astGather sh4 w (vars4, ix4))
    Ast.AstSum snat _ v ->
      let perm3 = backpermCycle $ valueOf @p' + 1
          perm4 = permCycle $ valueOf @m' + 1
          (sh41, sh42) = splitAt_Shape @m' sh4
          sh5 = sh41 `shrAppend` (lengthAst v :$: sh42)
          innerGather = astGather sh5 (astTranspose perm3 v) (vars4, ix4)
      in astSum snat stensorKind
         $ if not (knobExpand knobs) || length perm4 <= valueOf @m'
           then astTranspose perm4 innerGather
           else astTransposeAsGather knobs perm4 innerGather
    Ast.AstReplicate snat STKR{} v | AstConcrete _ (RepN it) <- i4 ->
      let i = fromIntegral it
      in if 0 <= i && i < sNatValue snat
         then astGather sh4 v (vars4, rest4)
         else case ftkAst v of
           FTKR _ x ->
             let ftk = FTKR sh4 x
             in fromPrimal $ AstConcrete ftk (constantTarget def ftk)
    Ast.AstReplicate _ STKR{} v -> astGather sh4 v (vars4, rest4)
    Ast.AstBuild1{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstLet var u v -> astLet var u (astGatherCase sh4 v (vars4, ix4))

    AstSumOfList{} -> Ast.AstGather sh4 v4 (vars4, ix4)

    Ast.AstMinIndexR v ->
      Ast.AstMinIndexR
      $ astGatherKnobsR knobs
          (sh4 `shrAppend` (shrLast (shapeAst v) :$: ZSR))
          v (vars4, ix4)
    Ast.AstMaxIndexR v ->
      Ast.AstMaxIndexR
      $ astGatherKnobsR knobs
          (sh4 `shrAppend` (shrLast (shapeAst v) :$: ZSR))
          v (vars4, ix4)
    Ast.AstFloorR v ->
      Ast.AstFloorR
      $ astGatherKnobsR knobs sh4 v (vars4, ix4)
    Ast.AstIotaR{}
     | AstConcrete _ (RepN i) <- i4 -> case sameNat (Proxy @p') (Proxy @1) of
      Just Refl -> astFromIntegralR $ astReplicate0N sh4 i
      _ -> error "astGather: AstIotaR: impossible pattern needlessly required"
    Ast.AstIotaR{} ->  -- probably nothing can be simplified; a normal form
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
    Ast.AstIndex v2 ix2 -> case (v2, ix2) of
      (Ast.AstFromVector{}, i2 :.: ZIR) -> astGather sh4 v2 (vars4, i2 :.: ix4)
      _ ->  -- AstVar, AstConcrete
        Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstScatter @_ @n7 (_ :$: sh)
                   v (vars, AstIntVar var5 :.: (ix2 :: AstIxR AstMethodLet p71))
      | AstIntVar var6 <- i4, var6 == var5 ->
          gcastWith (unsafeCoerceRefl :: p1' + n' :~: p71 + n7) $
          astGather sh4 (astScatter sh v (vars, ix2))
                        (vars4, rest4)
    Ast.AstScatter @_ @n7 (_ :$: sh)
                   v (vars, AstConcrete _ i5 :.: (ix2 :: AstIxR AstMethodLet p71))
      | AstConcrete _ i6 <- i4
      , STKScalar{} <- stensorKind @r ->
          gcastWith (unsafeCoerceRefl :: p1' + n' :~: p71 + n7) $
          if i6 == i5
          then astGather sh4 (astScatter sh v (vars, ix2)) (vars4, rest4)
          else astReplicate0N sh4 def
    Ast.AstScatter{} ->  -- normal form
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstFromVector @y2 snat l | AstConcrete _ (RepN it) <- i4
                                 , STKR{} <- stensorKind @y2 ->
      let i = fromIntegral it
      in if 0 <= i && i < sNatValue snat
         then astGather sh4 (l V.! i) (vars4, rest4)
         else case ftkAst v4 of
           FTKR _ x ->
             let ftk = FTKR sh4 x
             in fromPrimal $ AstConcrete ftk (constantTarget def ftk)
    Ast.AstFromVector{} | gatherFromNF vars4 ix4 ->  -- normal form
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstFromVector @y2 snat l | STKR{} <- stensorKind @y2 ->
      -- Term rest4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use tlet.
      funToVarsIx (valueOf @m') $ \ (!varsFresh, IxR !ixFresh) ->
        let f v = astGatherRec sh4 v (vars4, rest4)
            -- This subst doesn't currently break sharing because it's a rename.
            subst i =
              foldr (\(i2, var2) v2 ->
                      substituteAst i2 var2 v2)
                    i
                    (zipSized ixFresh vars4)
            i5 = subst i4
       in astGather sh4 (astFromVector snat $ V.map f l) (varsFresh, i5 :.: IxR ixFresh)
    Ast.AstAppend u v ->
      let ulen = AstConcrete FTKScalar $ RepN $ fromIntegral $ lengthAst u
          iu = simplifyAstInt (AstN2 MinusOp i4 ulen)
      in case simplifyAstBool $ Ast.AstRel LsOp i4 ulen of
        AstBoolConst b -> if b
                          then astGather sh4 u (vars4, i4 :.: rest4)
                          else astGather sh4 v (vars4, iu :.: rest4)
        bExpr ->
          funToVarsIx (valueOf @m') $ \ (!varsFresh, IxR !ixFresh) ->
            let u2 = astGatherRec sh4 u (vars4, i4 :.: rest4)
                v2 = astGatherRec sh4 v (vars4, iu :.: rest4)
                -- This subst doesn't break sharing because it's a rename.
                subst i =
                  foldr (uncurry substituteAstBool) i
                        (zipSized ixFresh vars4)
                bExpr5 = subst bExpr
            in astGather sh4 (astFromVector (SNat @2) $ V.fromList [u2, v2])
                             (varsFresh, astCond bExpr5 0 1 :.: IxR ixFresh)
    Ast.AstSlice i _k v ->
      let ii = simplifyAstInt (i4 + fromIntegral i)
        -- we generate this index, so we simplify on the spot
      in astGather sh4 v (vars4, ii :.: rest4)
    Ast.AstReverse v ->
      let iRev = simplifyAstInt (fromIntegral (lengthAst v - 1) - i4)
        -- we generate this index, so we simplify on the spot
      in astGather sh4 v (vars4, iRev :.: rest4)
    Ast.AstTranspose perm v | valueOf @p' >= length perm ->
      astGather sh4 v (vars4, ixrPermutePrefix (permRInverse perm) ix4)
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
      let substLet :: AstIxR AstMethodLet m7 -> AstVarList m7
                   -> AstInt AstMethodLet
                   -> AstInt AstMethodLet
          substLet (IxR ix) vars i =
            simplifyAstInt  -- we generate the index, so we simplify on the spot
            $ foldr (uncurry astLetInt) i
                    (zipSized vars ix)
          composedGather :: p' <= m2 => AstTensor AstMethodLet s (TKR2 (m' + n') r)
          composedGather =
            let (vars2p, vars22) = splitAt_SizedS @p' @(m2 - p') vars2
                ix22 = fmap (substLet ix4 vars2p) ix2
            in gcastWith (unsafeCoerceRefl :: m2 + n2 - p' :~: n') $
               astGather sh4 v2 (vars4 `listrAppend` vars22, ix22)
          assimilatedGather :: m2 <= p' => AstTensor AstMethodLet s (TKR2 (m' + n') r)
          assimilatedGather =
            let (ix42, ix44) = splitAt_Index @m2 @(p' - m2) ix4
                ix22 = fmap (substLet ix42 vars2) ix2
            in gcastWith (unsafeCoerceRefl :: n' + p' - m2 :~: n2) $
               astGather sh4 v2 (vars4, ix22  `ixrAppend` ix44)
      in case cmpNat (Proxy @p') (Proxy @m2) of
        LTI -> composedGather
        EQI -> assimilatedGather
        GTI -> gcastWith (flipCompare @p' @m2) assimilatedGather
    Ast.AstCastR v -> astCastR $ astGather sh4 v (vars4, ix4)
    Ast.AstFromIntegralR v -> astFromIntegralR $ astGather sh4 v (vars4, ix4)
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
         gcastWith (unsafeCoerceRefl :: sh :~: p_take ++ p_drop) $
         gcastWith (unsafeCoerceRefl :: p_take :~: Take p' sh) $
         gcastWith (unsafeCoerceRefl :: p_drop :~: Drop p' sh) $
         gcastWith (unsafeCoerceRefl :: X.Rank sh :~: p' + n') $
         astRFromS $ astGatherStepS @_ @p' @sh v
                     ( ShapedList.listToSized $ sizedToList vars4
                     , ShapedList.listToSized $ indexToList ix4 ) -}
    Ast.AstZipR _v -> error "TODO"

    Ast.AstApply{} -> Ast.AstGather sh4 v4 (vars4, ix4)

    -- The below should not appear here unless via wacky tests.
    Ast.AstReplicate0NR{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstSum0R{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstDot0R{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstDot1InR{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstMatvecmulR{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstMatmul2R{} -> Ast.AstGather sh4 v4 (vars4, ix4)

gatherFromNF :: forall m p. (KnownNat m, KnownNat p)
             => AstVarList m -> AstIxR AstMethodLet (1 + p) -> Bool
gatherFromNF _ ZIR = error "gatherFromNF: impossible pattern needlessly required"
gatherFromNF vars (i :.: rest) = case cmpNat (Proxy @p) (Proxy @m) of
  LTI ->
    let cmp (AstIntVar var1, AstIntVar var2) = var1 == var2
        cmp _ = False
        (varsP, varsPM) = splitAt_SizedS @p @(m - p) vars
    in all cmp (zipIndex rest (IxR (fmap AstIntVar varsP)))
       && not (any (`varNameInAst` i) varsPM)
  EQI ->
    let cmp (AstIntVar var1, AstIntVar var2) = var1 == var2
        cmp _ = False
    in all cmp (zipIndex rest (IxR (fmap AstIntVar vars)))
  GTI -> False

flipCompare :: forall (a :: Nat) b. Compare a b ~ GT => Compare b a :~: LT
flipCompare = unsafeCoerceRefl

isVar :: AstTensor AstMethodLet s y -> Bool
isVar Ast.AstVar{} = True
isVar (Ast.AstFromPrimal Ast.AstVar{}) = True
isVar (Ast.AstPrimalPart Ast.AstVar{}) = True
isVar (Ast.AstDualPart Ast.AstVar{}) = True
isVar _ = False

astGatherKnobsS
  :: forall shm shn shp r s.
     (KnownShS shm, KnownShS shn, KnownShS shp, TensorKind r, AstSpan s)
  => SimplifyKnobs
  -> AstTensor AstMethodLet s (TKS2 (shp ++ shn) r)
  -> (AstVarListS shm, AstIxS AstMethodLet shp)
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
astGatherKnobsS knobs v0 (vars0, ix0) =
  case (knownShS @shm, (vars0, ix0)) of
    _ | any (`varNameInAst` v0) $ toList vars0 ->
      error $ "astGatherS: gather vars in v0: "
              ++ show (vars0, v0)
    (_, (ZS, _)) -> astIndex v0 ix0
    (_, (_, ZIS)) -> if knobExpand knobs
                     then Ast.AstGatherS v0 (vars0, ix0)
                     else astReplicateNS @shm @shn v0
    (shm@((:$$) @_ @sh' k sh'), (var ::$ vars, i1 :.$ rest1)) ->
      if | not (any (`varNameInAst` i1) $ toList vars0) ->
           withKnownShS (shsTail (knownShS @shp)) $
           withKnownShS (shsTail (knownShS @shp) `shsAppend` knownShS @shn) $
           astGatherKnobsS @shm @shn @(Tail shp)
                           knobs (astIndex v0 (i1 :.$ ZIS))
                           (vars0, rest1)
         | case iN of
             AstIntVar varN' ->
               varN' == getConst varN
               && not (any (getConst varN `varNameInAst`) restN)
             _ -> False
         , kN@SNat <- shsLast shm
         , vkN@SNat <- shsLast (knownShS @shp)
         , case geq kN vkN of
             Just Refl -> True
             _ -> False
           -> gcastWith (unsafeCoerceRefl
                         :: Init shp ++ (Last shm ': shn) :~: shp ++ shn) $
              gcastWith (unsafeCoerceRefl
                         :: Init shm ++ (Last shm ': shn) :~: shm ++ shn) $
              withKnownShS (shsInit shm) $
              withKnownShS (shsInit (knownShS @shp)) $
              astGatherKnobsS @(Init shm) @(Last shm ': shn) @(Init shp)
                              knobs v0 (varsN, restN)
         | varInIndexS (varNameToAstVarId $ getConst var) ix0 ->
           astGatherCase @shm @shn @shp v0 (vars0, ix0)
         | otherwise ->
           if knobExpand knobs
           then Ast.AstGatherS @shm @shn @shp v0 (vars0, ix0)
           else withKnownShS sh' $
                withKnownShS (knownShS @sh' `shsAppend` knownShS @shn) $
                astReplicate k stensorKind
                             (astGatherKnobsS @(Tail shm) @shn @shp
                                              knobs v0 (vars, ix0))
       where
        restN = ixsInit ix0
        iN = ixsLast ix0
        varsN = listsInit vars0
        varN = listsLast vars0
 where
  astIndex
    :: forall shm' shn' s'.
       (KnownShS shm', KnownShS shn', AstSpan s')
    => AstTensor AstMethodLet s' (TKS2 (shm' ++ shn') r)
    -> AstIxS AstMethodLet shm'
    -> AstTensor AstMethodLet s' (TKS2 shn' r)
  astIndex v2 ix2 =
    withKnownShS (knownShS @shm' `shsAppend` knownShS @shn') $
    if knobStepOnly knobs
    then astIndexKnobsS knobs (astNonIndexStep v2) (simplifyAstIxS ix2)
    else astIndexKnobsS knobs v2 ix2
  astGatherRec, astGather
    :: forall shm' shn' shp' s' r'.
       (KnownShS shm', KnownShS shn', KnownShS shp', AstSpan s', TensorKind r')
    => AstTensor AstMethodLet s' (TKS2 (shp' ++ shn') r')
    -> (AstVarListS shm', AstIxS AstMethodLet shp')
    -> AstTensor AstMethodLet s' (TKS2 (shm' ++ shn') r')
  astGatherRec v2 (vars2, ix2) =
    withKnownShS (knownShS @shp' `shsAppend` knownShS @shn') $
    if knobStepOnly knobs
    then Ast.AstGatherS @shm' @shn' @shp' v2 (vars2, ix2)
    else astGatherKnobsS @shm' @shn' @shp' knobs v2 (vars2, ix2)
  astGather v2 (vars2, ix2) =
    withKnownShS (knownShS @shp' `shsAppend` knownShS @shn') $
    if knobStepOnly knobs
    then astGatherKnobsS @shm' @shn' @shp'
                         knobs
                         (astNonIndexStep v2)
                         (vars2, simplifyAstIxS ix2)
    else astGatherKnobsS @shm' @shn' @shp' knobs v2 (vars2, ix2)
  -- Note that v4 is in weak head normal form and so can't one-step reduce
  -- and so we don't have to reduce it to expose any top redexes.
  astGatherCase
    :: forall shm' shn' shp'.
       (KnownShS shm', KnownShS shn', KnownShS shp')
    => AstTensor AstMethodLet s (TKS2 (shp' ++ shn') r)
    -> (AstVarListS shm', AstIxS AstMethodLet shp')
    -> AstTensor AstMethodLet s (TKS2 (shm' ++ shn') r)
  astGatherCase v4 (_, ZIS) = astReplicateNS @shm' @shn' v4  -- not really possible
  astGatherCase v4 ( vars4
                   , ix4@((:.$) @p1' @shp1' i4 rest4) )
                | Dict <- shsKnownShS (knownShS @shm' `shsAppend` knownShS @shn')
                , Dict <- sixKnown rest4 = case v4 of
    Ast.AstProject1{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstProject2{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstApply{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstVar{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstPrimalPart{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstDualPart{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstFromPrimal v ->
      Ast.AstFromPrimal $ astGather @shm' @shn' @shp' v (vars4, ix4)
    Ast.AstD u u' ->
      -- Term ix4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use tlet.
      -- Also, the sharing would be dissolved by the substitution, anyway,
      -- and the same subsitution would be unsound with sharing.
      funToVarsIxS @shm' $ \ (!varsFresh, IxS !ixFresh) ->
        -- This subst doesn't currently break sharing, because it's a rename.
        let subst i =
              foldr (\(i2, var2) v2 -> substituteAst i2 var2 v2)
                    i
                    (toList $ zipSizedS ixFresh vars4)
            ix5 = fmap subst ix4
        in Ast.AstD (astGatherRec @shm' @shn' @shp' u (vars4, ix4))
                    (astGatherRec @shm' @shn' @shp' u' (varsFresh, ix5))
    Ast.AstCond b v w ->
      astCond b (astGather @shm' @shn' @shp' v (vars4, ix4))
                (astGather @shm' @shn' @shp' w (vars4, ix4))
    Ast.AstFromVector @y2 snat l | AstConcrete _ (RepN it) <- i4
                                 , STKS{} <- stensorKind @y2 ->
      let i = fromIntegral it
      in if 0 <= i && i < sNatValue snat
         then astGather @shm' @shn' @shp1' (l V.! i) (vars4, rest4)
         else case ftkAst v4 of
           FTKS _ x ->
             let ftk = FTKS knownShS x
             in fromPrimal $ AstConcrete ftk (constantTarget def ftk)
    Ast.AstFromVector{} | gatherFromNFS vars4 ix4 ->  -- normal form,
                                                      -- STKScalar case included
      Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstFromVector @y2 snat l | STKS{} <- stensorKind @y2 ->
      -- Term rest4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use tlet.
      funToVarsIxS @shm' $ \ (!varsFresh, IxS !ixFresh) ->
        let f v = astGatherRec @shm' @shn' @shp1' v (vars4, rest4)
            -- This subst doesn't currently break sharing because it's a rename.
            subst i =
              foldr (\(i2, var2) v2 ->
                      substituteAst i2 var2 v2)
                    i
                    (toList $ zipSizedS ixFresh vars4)
            i5 = subst i4
       in astGather @shm' @shn' @(p1' ': shm')
                    (astFromVector snat $ V.map f l)
                    (varsFresh, i5 :.$ IxS ixFresh)
    Ast.AstFromVector{} -> error "astGatherCase: impossible case"
    Ast.AstSum snat@(SNat @n1) _ v ->
      let perm3 = backpermCycle $ shsLength (knownShS @shp') + 1
          perm4 = permCycle $ shsLength (knownShS @shm') + 1
      in Permutation.permFromList perm3 $ \(perm3S :: Permutation.Perm perm3P) ->
         gcastWith (unsafeCoerceRefl
                    :: Compare (Rank perm3P) (Rank (n1 : shp' ++ shn'))
                       :~: LT) $
         gcastWith (unsafeCoerceRefl
                    :: Permutation.PermutePrefix perm3P (n1 : (shp' ++ shn'))
                       :~: shp' ++ (n1 : shn')) $
         trustMeThisIsAPermutation @perm3P $
         Permutation.permFromList perm4 $ \(perm4S :: Permutation.Perm perm4P) ->
         gcastWith (unsafeCoerceRefl
                    :: Compare (Rank perm4P) (Rank (shm' ++ (n1 : shn')))
                       :~: LT) $
         gcastWith (unsafeCoerceRefl
                    :: Permutation.PermutePrefix perm4P (shm' ++ (n1 : shn'))
                       :~: n1 : (shm' ++ shn')) $
         trustMeThisIsAPermutation @perm4P $
         withKnownShS (knownShS @shp' `shsAppend` (knownShS @shn')) $
         withKnownShS (knownShS @shm' `shsAppend` (snat :$$ knownShS @shn')) $
         let innerGather =
               astGather @shm' @(n1 : shn') @shp'
                         (astTransposeS perm3S v) (vars4, ix4)
         in astSum snat stensorKind
            $ if not (knobExpand knobs)
                 || length perm4 <= shsLength (knownShS @shm')
              then astTransposeS perm4S innerGather
              else astTransposeAsGatherS knobs perm4S innerGather
    Ast.AstReplicate snat STKS{} v | AstConcrete _ (RepN it) <- i4 ->
      let i = fromIntegral it
      in if 0 <= i && i < sNatValue snat
         then astGather @shm' @shn' @shp1' v (vars4, rest4)
         else case ftkAst v of
           FTKS _ x ->
             let ftk = FTKS knownShS x
             in fromPrimal $ AstConcrete ftk (constantTarget def ftk)
    Ast.AstReplicate _ STKS{} v ->
      astGather @shm' @shn' @shp1' v (vars4, rest4)
    Ast.AstReplicate _ STKScalar{} v | ZIS <- rest4 ->
      astGather @shm' @shn' @shp1' (astFromScalar v) (vars4, rest4)
    Ast.AstBuild1{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstLet var u v ->
      astLet var u (astGatherCase @shm' @shn' @shp' v (vars4, ix4))
    AstConcrete{} ->  -- free variables possible, so can't compute the tensor
      Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)

    AstSumOfList{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)

    AstN1S opCode v | not (isVar v) ->
      AstN1S opCode (astGatherRec @shm' @shn' @shp' v (vars4, ix4))
    AstN1S{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    AstN2S{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
      -- Going inside AstN2R usually makes the term more expensive to interpret
      -- and reverting this transformation requires comparing two arguments,
      -- so it's not practical.
    Ast.AstR1S opCode v | not (isVar v) ->
      Ast.AstR1S opCode (astGatherRec @shm' @shn' @shp' v (vars4, ix4))
    Ast.AstR1S{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstR2S{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstI2S{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstFloorS v ->
      Ast.AstFloorS
      $ astGatherKnobsS @shm' @shn' @shp' knobs v (vars4, ix4)
    Ast.AstFromIntegralS v ->
      astFromIntegralS $ astGather @shm' @shn' @shp' v (vars4, ix4)
    Ast.AstCastS v -> astCastS $ astGather @shm' @shn' @shp' v (vars4, ix4)
    Ast.AstMinIndexS @sh @n v -> case shsLast (SNat @n :$$ knownShS @sh) of
      nl@SNat ->
        let shnl = knownShS @shn' `shsAppend` (nl :$$ ZSS)
        in gcastWith (unsafeCoerceRefl
                     :: shp' ++ (shn' ++ '[Last (n : sh)]) :~: n ': sh) $
           gcastWith (unsafeCoerceRefl
                      :: Head (shm' ++ (shn' ++ '[Last (n : sh)]))
                         ': (Tail (shm' ++ (shn' ++ '[Last (n : sh)])))
                         :~: shm' ++ (shn' ++ '[Last (n : sh)])) $
           gcastWith (unsafeCoerceRefl
                      :: Init (shm' ++ (shn' ++ '[Last (n : sh)]))
                      :~: shm' ++ shn') $
           withKnownShS shnl $
           withKnownNat (shsHead (knownShS @shm' `shsAppend` shnl)) $
           withKnownShS (shsTail (knownShS @shm' `shsAppend` shnl)) $
           Ast.AstMinIndexS @(Tail (shm' ++ (shn' ++ '[Last (n : sh)])))
                            @(Head (shm' ++ (shn' ++ '[Last (n : sh)])))
           $ astGatherKnobsS @shm' @(shn' ++ '[Last (n : sh)]) @shp'
                             knobs v (vars4, ix4)
    Ast.AstMaxIndexS @sh @n v -> case shsLast (SNat @n :$$ knownShS @sh) of
      nl@SNat ->
        let shnl = knownShS @shn' `shsAppend` (nl :$$ ZSS)
        in gcastWith (unsafeCoerceRefl
                     :: shp' ++ (shn' ++ '[Last (n : sh)]) :~: n ': sh) $
           gcastWith (unsafeCoerceRefl
                      :: Head (shm' ++ (shn' ++ '[Last (n : sh)]))
                         ': (Tail (shm' ++ (shn' ++ '[Last (n : sh)])))
                         :~: shm' ++ (shn' ++ '[Last (n : sh)])) $
           gcastWith (unsafeCoerceRefl
                      :: Init (shm' ++ (shn' ++ '[Last (n : sh)]))
                      :~: shm' ++ shn') $
           withKnownShS shnl $
           withKnownNat (shsHead (knownShS @shm' `shsAppend` shnl)) $
           withKnownShS (shsTail (knownShS @shm' `shsAppend` shnl)) $
           Ast.AstMaxIndexS @(Tail (shm' ++ (shn' ++ '[Last (n : sh)])))
                            @(Head (shm' ++ (shn' ++ '[Last (n : sh)])))
           $ astGatherKnobsS @shm' @(shn' ++ '[Last (n : sh)]) @shp'
                             knobs v (vars4, ix4)
    Ast.AstIotaS | AstConcrete _ (RepN i) <- i4 ->
      astFromIntegralS $ astReplicate0NS i
    Ast.AstIotaS ->  -- probably nothing can be simplified; a normal form
      Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstIndexS @shm2 v2 ix2 -> case (v2, ix2) of
      (Ast.AstFromVector{}, i2 :.$ ZIS) ->
        astGather @shm' @shn' @(shm2 ++ shp') v2 (vars4, i2 :.$ ix4)
      _ ->  -- AstVar, AstConcrete
        Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstScatterS @shm7 @shn7 @shp7 v (vars, AstIntVar var5 :.$ ix2)
      | AstIntVar var6 <- i4, var6 == var5
      , Dict <- sixKnown ix2 ->
          astGather @shm' @shn' @shp1'
                    (astScatterS @shm7 @shn7 @(Tail shp7)
                                 v (vars, ix2))
                    (vars4, rest4)
    Ast.AstScatterS @shm7 @shn7 @shp7 v (vars, AstConcrete _ i5 :.$ ix2)
      | AstConcrete _ i6 <- i4
      , Dict <- sixKnown ix2
      , STKScalar{} <- stensorKind @r ->
          if i6 == i5
          then astGather @shm' @shn' @shp1'
                         (astScatterS @shm7 @shn7 @(Tail shp7)
                                      v (vars, ix2))
                         (vars4, rest4)
          else astReplicate0NS def  -- TODO: or 0? review again and comment
    Ast.AstScatterS{} ->  -- normal form
      Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstAppendS @m u v ->
      let ulen = AstConcrete FTKScalar $ RepN $ valueOf @m
          iu = simplifyAstInt (AstN2 MinusOp i4 ulen)
      in case simplifyAstBool $ Ast.AstRel LsOp i4 ulen of
        AstBoolConst b -> if b
                          then astGather @shm' @shn' u (vars4, i4 :.$ rest4)
                          else astGather @shm' @shn' v (vars4, iu :.$ rest4)
        bExpr ->
          funToVarsIxS @shm' $ \ (!varsFresh, IxS !ixFresh) ->
            let u2 = astGatherRec @shm' @shn' u (vars4, i4 :.$ rest4)
                v2 = astGatherRec @shm' @shn' v (vars4, iu :.$ rest4)
                -- This subst doesn't break sharing because it's a rename.
                subst i =
                  foldr (uncurry substituteAstBool) i
                        (toList $ zipSizedS ixFresh vars4)
                bExpr5 = subst bExpr
            in astGather @shm' @shn' @(2 ': shm')
                         (astFromVector (SNat @2) $ V.fromList [u2, v2])
                         (varsFresh, astCond bExpr5 0 1 :.$ IxS ixFresh)
    Ast.AstSliceS @i v ->
      let ii = simplifyAstInt (i4 + valueOf @i)
        -- we generate this index, so we simplify on the spot
      in astGather @shm' @shn' v (vars4, ii :.$ rest4)
    Ast.AstReverseS @n v ->
      let iRev = simplifyAstInt ((valueOf @n - 1) - i4)
        -- we generate this index, so we simplify on the spot
      in astGather @shm' @shn' v (vars4, iRev :.$ rest4)
    Ast.AstTransposeS @perm @sh perm v ->
      let rankPerm = Permutation.permRank perm
      in case gcompare (shsRank $ knownShS @shp') rankPerm of
        GLT ->  -- TODO: this does not provide any proof, so use cmpNat :(
          if knobExpand knobs
          then astGather @shm' @shn' @shp'
                         (astTransposeAsGatherS knobs perm v) (vars4, ix4)
          else Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
        _ ->
          gcastWith (lemRankMapJust $ shsTakeLen perm (knownShS @sh)) $
          gcastWith (unsafeCoerceRefl :: Rank (TakeLen perm sh) :~: Rank perm) $
          permInverse perm
          $ \ (invperm :: Nested.Perm invperm) proof ->
            case proof (ssxFromShape $ shCvtSX
                        $ shsTakeLen perm (knownShS @sh)) of
              Refl ->
                -- from PermutePrefix and ranks:
                gcastWith
                  (unsafeCoerceRefl
                   :: Permutation.PermutePrefix invperm shp' ++ shn'
                      :~: Permutation.PermutePrefix invperm (shp' ++ shn')) $
                -- from AstTransposeS:
--                gcastWith
--                  (unsafeCoerceRefl
--                   :: Permutation.PermutePrefix invperm (shp' ++ shn')
--                      :~: Permutation.PermutePrefix invperm (Permutation.PermutePrefix perm sh)) $
                -- from PermutePrefix:
--                gcastWith
--                  (unsafeCoerceRefl
--                   :: Permutation.PermutePrefix invperm (Permutation.PermutePrefix perm sh)
--                      :~: {-1-} Permutation.Permute invperm (TakeLen invperm (Permutation.PermutePrefix perm sh))
--                          ++ {-2-} DropLen invperm (Permutation.PermutePrefix perm sh)) $
                -- 1. from PermutePrefix:
--                gcastWith
--                  (unsafeCoerceRefl
--                   :: Permutation.Permute invperm (TakeLen invperm (Permutation.PermutePrefix perm sh))
--                      :~: Permutation.Permute invperm (TakeLen invperm (Permutation.Permute perm (TakeLen perm sh) ++ DropLen perm sh))) $
                -- ranks
                gcastWith
                  (unsafeCoerceRefl
                   :: Permutation.Permute invperm (TakeLen invperm (Permutation.Permute perm (TakeLen perm sh) ++ DropLen perm sh))
                      :~: Permutation.Permute invperm (Permutation.Permute perm (TakeLen perm sh))) $
                -- from permInverse but MapJust-unwrapped:
                gcastWith
                  (unsafeCoerceRefl
                   :: Permutation.Permute invperm (Permutation.Permute perm (TakeLen perm sh))
                      :~: TakeLen perm sh) $
                -- end of 1.
                -- 2. from PermutePrefix
--                gcastWith
--                  (unsafeCoerceRefl
--                   :: DropLen invperm (Permutation.PermutePrefix perm sh)
--                      :~: DropLen invperm (Permutation.Permute perm (TakeLen perm sh) ++ DropLen perm sh)) $
                -- ranks
                gcastWith
                  (unsafeCoerceRefl
                   :: DropLen invperm (Permutation.Permute perm (TakeLen perm sh) ++ DropLen perm sh)
                      :~: DropLen perm sh) $
                -- end of 2.
                -- from TakeLen:
                gcastWith
                  (unsafeCoerceRefl
                   :: TakeLen perm sh ++ DropLen perm sh :~: sh) $
                let invix4 = ixsPermutePrefix invperm ix4
                in case sixKnown invix4 of
                  Dict -> astGather @shm' @shn'
                                    @(Permutation.PermutePrefix invperm shp')
                                    v (vars4, invix4)
    Ast.AstReshapeS v ->
      if knobExpand knobs
      then astGather @shm' @shn' @shp' (astReshapeAsGatherS knobs v) (vars4, ix4)
      else Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstGatherS @shm2 @shn2 @shp2 v2 (vars2, ix2)
                   | SNat @rank4 <- ixsRank ix4
                   , SNat @rank2 <- listsRank vars2 ->
      -- Term ix4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use tlet.
      --
      -- Independently, we need to insert lets to each index element,
      -- bloating the term. TODO: would going via a rank 1 vector,
      -- as in tletIx help or would we need to switch indexes to vector
      -- altogether (terrible for user comfort, especially wrt typing).
      let substLet :: KnownShS shm7
                   => AstIxS AstMethodLet shm7 -> AstVarListS shm7
                   -> AstInt AstMethodLet
                   -> AstInt AstMethodLet
          substLet (IxS ix) vars i =
            simplifyAstInt  -- we generate the index, so we simplify on the spot
            $ foldr (uncurry astLetInt) i
                    (toList $ zipSizedS vars ix)
          IxS list4 = ix4
          composedGather ::  -- rank4 <= rank2
                            AstTensor AstMethodLet s (TKS2 (shm' ++ shn') r)
          composedGather =
            -- we have: shm2 ++ shn2 == shp' ++ shn'
            -- so from ranks:
            gcastWith (unsafeCoerceRefl :: TakeLen shp' shm2 :~: shp') $
            -- and from congruence:
--            gcastWith (unsafeCoerceRefl
--                       :: DropLen shp' shm2 ++ shn2 :~: shn') $
            -- from congruence:
            gcastWith (unsafeCoerceRefl
                       :: (shm' ++ DropLen shp' shm2) ++ shn2 :~: shm' ++ shn') $
            let vars2p = listsTakeLen list4 vars2
                vars22 = listsDropLen list4 vars2
                ix22 = fmap (substLet ix4 vars2p) ix2
                list422 = vars4 `listsAppend` vars22
            in case slistKnown list422 of
              Dict -> astGather @_ @shn2 @shp2 v2 (list422, ix22)
          assimilatedGather ::  -- rank2 <= rank4
                               AstTensor AstMethodLet s (TKS2 (shm' ++ shn') r)
          assimilatedGather =
            -- we have: shm2 ++ shn2 == shp' ++ shn'
            -- so from ranks:
            gcastWith (unsafeCoerceRefl :: TakeLen shm2 shp' :~: shm2) $
            -- and from congruence:
--            gcastWith (unsafeCoerceRefl
--                       :: DropLen shm2 shp' ++ shn' :~: shn2) $
            -- from congruence:
            gcastWith (unsafeCoerceRefl
                       :: (shp2 ++ DropLen shm2 shp') ++ shn' :~: shp2 ++ shn2) $
            let ix42 = IxS $ listsTakeLen vars2 list4
                ix44 = IxS $ listsDropLen vars2 list4
                ix22 = fmap (substLet ix42 vars2) ix2
                ix2244 = ix22 `ixsAppend` ix44
            in case sixKnown ix2244 of
              Dict -> astGather @shm' @shn' v2 (vars4, ix2244)
      in case cmpNat (Proxy @rank4) (Proxy @rank2) of
        LTI -> composedGather
        EQI -> assimilatedGather
        GTI -> gcastWith (flipCompare @rank4 @rank2) assimilatedGather
    Ast.AstZipS _v -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)

    -- These conversions need to stay down.
    Ast.AstSFromR{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstSFromX{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)

    -- These should not appear here unless via wacky tests.
    Ast.AstReplicate0NS{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
--    Ast.AstSum0S{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
--    Ast.AstDot0S{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstDot1InS{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstMatvecmulS{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstMatmul2S{} -> Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)

    Ast.AstProjectS{} ->  -- TODO, but most likely reduced before it gets here
      Ast.AstGatherS @shm' @shn' @shp' v4 (vars4, ix4)
    Ast.AstLetHVectorIn vars l v ->
      astLetHVectorIn vars l (astGatherCase @shm' @shn' @shp' v (vars4, ix4))

gatherFromNFS :: forall shm n shp. KnownShS shp
              => AstVarListS shm -> AstIxS AstMethodLet (n ': shp) -> Bool
gatherFromNFS vars (i :.$ IxS rest) =
  case gcompare (listsRank rest) (listsRank vars) of
    GGT -> False  -- this does not provide any proof, but it's fine
    _ ->
      let cmp (AstIntVar var1, AstIntVar var2) = var1 == var2
          cmp _ = False
          varsP = listsTakeLen rest vars
          varsPM = listsDropLen rest vars
          intVars = listsFmap (Const . AstIntVar . getConst) varsP
      in case (slistKnown varsP, slistKnown varsPM) of
        (Dict, Dict) -> case sameShape @(TakeLen shp shm) @shp of
          Just Refl -> all cmp (toList $ zipSizedS rest intVars)
                       && not (any (`varNameInAst` i) $ toList varsPM)
          Nothing -> False

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
            | otherwise -> astReplicate k (AstIxR v2 ix2)
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
astLet var u (Ast.AstRFromS v) = astRFromS $ astLet var u v
astLet var u (Ast.AstXFromS v) = astXFromS $ astLet var u v
astLet var u v = Ast.AstLet var u v

-- A special variant to bind integer expressions inside indexes.
-- It check if the bound variables appears in the body at all.
-- Normally, that's asymptotically worse than doing this
-- in a global inlining pass, but we assume indexes expressions
-- are short and we need them simple ASAP.
astLetInt :: IntVarName -> AstInt AstMethodLet -> AstInt AstMethodLet
          -> AstInt AstMethodLet
astLetInt var u v | var `varNameInAst` v = astLet var u v
astLetInt _ _ v = v

astCond :: TensorKind y
        => AstBool ms -> AstTensor ms s y -> AstTensor ms s y -> AstTensor ms s y
astCond (AstBoolConst b) v w = if b then v else w
astCond b (Ast.AstFromPrimal v) (Ast.AstFromPrimal w) =
  Ast.AstFromPrimal $ astCond b v w
-- TODO: astCond b (Ast.AstRFromS v) (Ast.AstRFromS w) = astRFromS $ astCond b v w
-- TODO: astCond b (Ast.AstXFromS v) (Ast.AstXFromS w) = astXFromS $ astCond b v w
astCond b v w = Ast.AstCond b v w

astSumOfList :: AstSpan s
             => STensorKindType y
             -> [AstTensor AstMethodLet s y]
             -> AstTensor AstMethodLet s y
astSumOfList stk l = case stk of
  STKScalar{} -> foldr1 (+) l  -- @sum@ breaks and also reverses order
  STKR SNat STKScalar{} -> foldr1 (+) l
  STKS sh STKScalar{} -> withKnownShS sh $ foldr1 (+) l
  STKX sh STKScalar{} -> withKnownShX sh $ foldr1 (+) l
  _ | Dict <- lemTensorKindOfSTK stk ->
    let v = V.fromList l
    in withSNat (V.length v) $ \snat ->
      astSum snat stk $ astFromVector snat v

-- TODO: fuse scatters, scatter and sum, perhaps more (fromList?)
astScatter :: forall m n p s r.
              (TensorKind r, KnownNat m, KnownNat n, KnownNat p, AstSpan s)
           => IShR (p + n) -> AstTensor AstMethodLet s (TKR2 (m + n) r)
           -> (AstVarList m, AstIxR AstMethodLet p)
           -> AstTensor AstMethodLet s (TKR2 (p + n) r)
astScatter _sh v (ZR, ZIR) = v
astScatter sh@(k :$: _) _v (_vars, AstConcrete _ (RepN it) :.: _ix)
  | let i = fromIntegral it
  , not (0 <= i && i < k)
  , STKScalar{} <- stensorKind @r =
      astReplicate0N sh def
-- else update (rzero sh 0) [AstConcreteS it] (astScatter ...)
astScatter sh v ((:::) @k var vars, ix)
  | not $ varNameToAstVarId var `varInIndex` ix =
    astScatter sh (astSum (SNat @k) stensorKind v) (vars, ix)
-- astScatter sh v (ZR, ix) = update (rzero sh 0) ix v
astScatter sh (Ast.AstFromPrimal v) (vars, ix) =
  Ast.AstFromPrimal $ astScatter sh v (vars, ix)
astScatter sh v (vars, ix) = Ast.AstScatter sh v (vars, ix)

-- TODO: fuse scatters, scatter and sum, perhaps more (fromList?)
astScatterS :: forall shm shn shp r s .
               (KnownShS shm, KnownShS shn, KnownShS shp, TensorKind r, AstSpan s)
            => AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
            -> (AstVarListS shm, AstIxS AstMethodLet shp)
            -> AstTensor AstMethodLet s (TKS2 (shp ++ shn) r)
astScatterS v (ZS, ZIS) = v
{- TODO: this is impossible, due to strongly typed index,
-- and checked when indexes are created, right?
astScatterS _v (_vars, (:.$) @k (AstConcrete _ (RepN it)) _ix)
  | let i = fromIntegral it
  , not (0 <= i && i < valueOf @k)
  , STKScalar{} <- stensorKind @r =
      astReplicate0NS def
-- else update (rzero sh 0) [AstConcreteS it] (astScatter ...) -}
astScatterS v (Const var ::$ (vars :: AstVarListS sh3), ix)
  | not $ varNameToAstVarId var `varInIndexS` ix
  , Dict <- slistKnown vars =
      withKnownShS (knownShS @sh3 `shsAppend` knownShS @shn) $
      astScatterS @sh3 @shn @shp (astSum SNat stensorKind v) (vars, ix)
-- astScatterS v (ZR, ix) = update (rzero sh 0) ix v
astScatterS (Ast.AstFromPrimal v) (vars, ix) =
  withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
  Ast.AstFromPrimal $ astScatterS @shm @shn @shp v (vars, ix)
astScatterS v (vars, ix) = Ast.AstScatterS @shm @shn @shp v (vars, ix)

astFromVector :: forall y k s. (TensorKind y, AstSpan s)
              => SNat k -> Data.Vector.Vector (AstTensor AstMethodLet s y)
              -> AstTensor AstMethodLet s (BuildTensorKind k y)
astFromVector snat v | Just Refl <- geq snat (SNat @1) =
  astReplicate (SNat @1) stensorKind (v V.! 0)
astFromVector snat l | Just Refl <- sameAstSpan @s @PrimalSpan =
  let unConst :: AstTensor AstMethodLet PrimalSpan y
              -> Maybe (FullTensorKind y, RepN y)
      unConst (AstConcrete ftk t) = Just (ftk, t)
      unConst _ = Nothing
  in case V.mapM unConst l of
    Just l4 | V.null l4 -> error "astFromVector: empty vector"
    Just l4 | Dict <- lemTensorKindOfBuild snat (stensorKind @y) ->
      let l3 = V.map snd l4
      in AstConcrete (buildFTK snat $ fst $ l4 V.! 0)
         $ tfromVector snat stensorKind l3
    _ -> Ast.AstFromVector snat l
astFromVector snat l | Just Refl <- sameAstSpan @s @FullSpan =
  let unFromPrimal :: AstTensor AstMethodLet FullSpan y
                   -> Maybe (AstTensor AstMethodLet PrimalSpan y)
      unFromPrimal (Ast.AstFromPrimal t) = Just t
      unFromPrimal _ = Nothing
  in case V.mapM unFromPrimal l of
    Just l2 | V.null l2 -> error "astFromVector: empty vector"
    Just l2 | Dict <- lemTensorKindOfBuild snat (stensorKind @y) ->
      Ast.AstFromPrimal $ astFromVector snat l2
    Nothing -> Ast.AstFromVector snat l
{- TODO:
astFromVector snat l | STKR{} <- stensorKind @y =
  let unFrom :: AstTensor AstMethodLet s (TKR2 (Rank sh) x)
             -> Maybe (AstTensor AstMethodLet s (TKS2 sh x))
      unFrom (Ast.AstRFromS t) = Just t
      unFrom _ = Nothing
  in case V.mapM unFrom l of
    Just l2 | V.null l2 -> error "astFromVector: empty vector"
    Just l2 | Dict <- lemTensorKindOfBuild snat (stensorKind @y) ->
      astRFromS $ astFromVector snat l2
    Nothing -> Ast.AstFromVector snat l -}
astFromVector snat l = Ast.AstFromVector snat l

astSum :: forall y k s. AstSpan s
       => SNat k -> STensorKindType y
       -> AstTensor AstMethodLet s (BuildTensorKind k y)
       -> AstTensor AstMethodLet s y
astSum snat@SNat stk t0 = case (stk, ftkAst t0) of
--  1 :$: rest -> astReshape rest t0  -- TODO: slows down the CNNO test
  (STKR{}, FTKR (0 :$: rest) FTKScalar) -> astReplicate0N rest 0
  (STKS{}, FTKS (SNat @n :$$ rest) FTKScalar)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
      withKnownShS rest
      $ astReplicate0NS 0
  _ -> case t0 of
    -- Ast.AstLet var u v -> astLet var u (astSum snat v)
      -- this is problematic, because it keeps huge tensors alive for longer
    Ast.AstReplicate snat2 (STKR SNat _) v | STKR _ STKScalar{} <- stk ->
      v * astReplicate0N (shapeAst v) (fromInteger $ fromSNat snat2)
    Ast.AstReplicate snat2 (STKS sh _) v | STKS _ STKScalar{} <- stk ->
     withKnownShS sh $
     v * astReplicate0NS (fromInteger $ fromSNat snat2)
    Ast.AstFromVector @y2 _ l ->
      gcastWith (unsafeCoerceRefl :: y2 :~: y) $
      case stk of
        STKScalar{} -> astSumOfList stk $ V.toList l
        STKR _ STKScalar{} -> astSumOfList stk $ V.toList l
        STKS _ STKScalar{} -> astSumOfList stk $ V.toList l
        STKX _ STKScalar{} -> astSumOfList stk $ V.toList l
        _ -> Ast.AstSum snat stk t0
    Ast.AstSlice _i 0 v | STKR _ STKScalar{} <- stk ->
      astReplicate0N (shrTail (shapeAst v)) 0
    Ast.AstSliceS @_ @k2 _v  | STKS _ STKScalar{} <- stk
                             , Just Refl <- sameNat (Proxy @k2) (Proxy @0) ->
      astReplicate0NS 0
    Ast.AstScatter (_ :$: sh) v (vars, _ :.: ix)
      | STKR{} <- stk ->
        astScatter sh v (vars, ix)
    Ast.AstScatterS @shm @shn @shp v (vars, _ :.$ ix)
      | STKS{} <- stk
      , Dict <- sixKnown ix ->
        astScatterS @shm @shn @(Tail shp) v (vars, ix)
    Ast.AstSlice i 1 v | STKR SNat _ <- stk ->
      astIndexR v (fromIntegral i :.: ZIR)
    Ast.AstSliceS @i @k2 v  | STKS{} <- stk
                            , Just Refl <- sameNat (Proxy @k2) (Proxy @1) ->
      astIndexS v (valueOf @i :.$ ZIS)
    Ast.AstReverse v | STKR{} <- stk -> astSum snat stk v
    Ast.AstReverseS v | STKS{} <- stk -> astSum snat stk v
    AstConcrete ftk t | Dict <- lemTensorKindOfSTK stk ->
      AstConcrete (razeFTK snat stensorKind ftk) $ tsum snat stk t
    Ast.AstFromPrimal v | Dict <- lemTensorKindOfSTK stk ->
      Ast.AstFromPrimal $ astSum snat stk v
    Ast.AstRFromS @sh v -> case stk of
      STKR _ x -> case knownShS @sh of
        (:$$) snat2 rest | Just Refl <- sameNat snat snat2 ->
          withKnownShS rest $
          astRFromS $ astSum snat (STKS rest x) v
        _ -> error "astSum: impossible shape"
    Ast.AstXFromS @sh v -> case stk of
      STKX @restx restx x -> case knownShS @sh of
        (:$$) @_ @rest snat2 rest | Just Refl <- sameNat snat snat2 ->
          gcastWith (unsafeCoerceRefl :: Rank restx :~: Rank rest) $
          withKnownShS rest $
          withKnownShX restx $
          astXFromS @rest @restx $ astSum snat (STKS rest x) v
        _ -> error "astSum: impossible shape"
    _ -> Ast.AstSum snat stk t0

astReplicate :: forall k y s. AstSpan s
             => SNat k -> STensorKindType y
             -> AstTensor AstMethodLet s y
             -> AstTensor AstMethodLet s (BuildTensorKind k y)
astReplicate snat@SNat stk
 | Dict <- lemTensorKindOfBuild snat stk = \case
{- TODO: these may be counterproductive with many gathers and their fusion
         though these let transpose cancel out with each other sometimes
         (instead we should try to cancel out inside replicate and only move
          if they don't) -}
  Ast.AstTranspose perm v ->
    astTranspose (0 : map succ perm) $ astReplicate snat stensorKind v
{- see the previous comment
  Ast.AstReshape sh v ->
    AstReshape (k :$: sh) $ astReplicate k v
-}
-- This allocates a big tensor too early, while it's still possible
-- a projection reduces this away. The cost to AD should not be too high.
-- This would also hide AstReplicate from hacks that recover tmatmul2, etc.
--  AstConcrete t -> AstConcrete $ treplicateR k t
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astReplicate snat stk v
  Ast.AstTransposeS @perm @sh1 perm v -> case stk of
    STKS @sh _ _ ->
      let zsuccPerm :: Permutation.Perm (0 : Permutation.MapSucc perm)
          zsuccPerm = Permutation.permShift1 perm
      in
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix (0 : Permutation.MapSucc perm) (k : sh1) :~: k : sh) $
        gcastWith (unsafeCoerceRefl :: Rank (0 : Permutation.MapSucc perm) :~: 1 + Rank perm) $
        trustMeThisIsAPermutation @(0 : Permutation.MapSucc perm) $
        astTransposeS zsuccPerm $ astReplicate snat stensorKind v
  Ast.AstRFromS v -> case stk of
    STKR _ x -> astRFromS $ astReplicate snat (STKS knownShS x) v
  Ast.AstXFromS v -> case stk of
    STKX _ x -> astXFromS $ astReplicate snat (STKS knownShS x) v
  v -> Ast.AstReplicate snat stk v

astReplicateN :: forall n p s r.
                 (KnownNat n, KnownNat p, TensorKind r, AstSpan s)
              => IShR (n + p) -> AstTensor AstMethodLet s (TKR2 p r)
              -> AstTensor AstMethodLet s (TKR2 (n + p) r)
astReplicateN sh v =
  let go :: IShR n' -> AstTensor AstMethodLet s (TKR2 (n' + p) r)
      go ZSR = v
      go (k :$: sh2) | SNat <- shrRank sh2 = withSNat k $ \snat ->
        astReplicate snat stensorKind $ go sh2
  in go (takeShape sh)

astReplicateNS :: forall shn shp s r.
                  (KnownShS shn, KnownShS shp, TensorKind r, AstSpan s)
               => AstTensor AstMethodLet s (TKS2 shp r)
               -> AstTensor AstMethodLet s (TKS2 (shn ++ shp) r)
astReplicateNS v =
  let go :: ShS shn' -> AstTensor AstMethodLet s (TKS2 (shn' ++ shp) r)
      go ZSS = v
      go ((:$$) @k @shn2 SNat shn2) | Dict <- shsKnownShS shn2 =
        withKnownShS (knownShS @shn2 `shsAppend` knownShS @shp) $
        astReplicate (SNat @k) stensorKind $ go shn2
  in go (knownShS @shn)

astReplicate0N :: forall n s r. (GoodScalar r, AstSpan s)
               => IShR n -> r -> AstTensor AstMethodLet s (TKR n r)
astReplicate0N sh =
  let go :: IShR n' -> AstTensor AstMethodLet s (TKR 0 r)
         -> AstTensor AstMethodLet s (TKR n' r)
      go ZSR v = v
      go (k :$: sh') v | SNat <- shrRank sh' = withSNat k $ \snat ->
        astReplicate snat stensorKind $ go sh' v
  in go sh . fromPrimal . AstConcrete (FTKR ZSR FTKScalar) . rscalar

astReplicate0NS :: forall shn s r. (KnownShS shn, GoodScalar r, AstSpan s)
                => r -> AstTensor AstMethodLet s (TKS shn r)
astReplicate0NS =
  let go :: ShS sh' -> AstTensor AstMethodLet s (TKS '[] r)
         -> AstTensor AstMethodLet s (TKS sh' r)
      go ZSS v = v
      go ((:$$) SNat sh') v | Dict <- shsKnownShS sh' =
        astReplicate SNat stensorKind $ go sh' v
  in go (knownShS @shn) . fromPrimal . AstConcrete (FTKS ZSS FTKScalar) . sscalar

astAppend :: (KnownNat n, TensorKind r, AstSpan s)
          => AstTensor AstMethodLet s (TKR2 (1 + n) r)
          -> AstTensor AstMethodLet s (TKR2 (1 + n) r)
          -> AstTensor AstMethodLet s (TKR2 (1 + n) r)
astAppend (AstConcrete (FTKR (ulen :$: sh) ftk2) u)
          (AstConcrete (FTKR (vlen :$: _) _) v) =
  AstConcrete (FTKR (ulen + vlen :$: sh) ftk2) $ rappend u v
astAppend (Ast.AstFromPrimal u) (Ast.AstFromPrimal v) =
  Ast.AstFromPrimal $ astAppend u v
astAppend (Ast.AstFromVector @y2 (SNat @k1) l1)
          (Ast.AstFromVector @y3 (SNat @k2) l2)
  | STKR{} <- stensorKind @y2
  , STKR{} <- stensorKind @y3 =
    astFromVector (SNat @(k1 + k2)) $ l1 V.++ l2
astAppend u v = Ast.AstAppend u v

astAppendS :: (KnownNat m, KnownNat n, KnownShS sh, TensorKind r, AstSpan s)
           => AstTensor AstMethodLet s (TKS2 (m ': sh) r)
           -> AstTensor AstMethodLet s (TKS2 (n ': sh) r)
           -> AstTensor AstMethodLet s (TKS2 ((m + n) ': sh) r)
astAppendS (AstConcrete (FTKS _ x) u) (AstConcrete _ v) =
  AstConcrete (FTKS knownShS x) $ sappend u v
astAppendS (Ast.AstFromPrimal u) (Ast.AstFromPrimal v) =
  Ast.AstFromPrimal $ astAppendS u v
astAppendS (Ast.AstFromVector @y2 (SNat @k1) l1)
           (Ast.AstFromVector @y3 (SNat @k2) l2)
  | STKS{} <- stensorKind @y2
  , STKS{} <- stensorKind @y3 =
    astFromVector (SNat @(k1 + k2)) $ l1 V.++ l2
astAppendS u v = Ast.AstAppendS u v

astSlice :: forall k s r. (KnownNat k, TensorKind r, AstSpan s)
         => Int -> Int -> AstTensor AstMethodLet s (TKR2 (1 + k) r)
         -> AstTensor AstMethodLet s (TKR2 (1 + k) r)
astSlice i n (AstConcrete (FTKR (_ :$: sh) ftk2) t) =
  AstConcrete (FTKR (n :$: sh) ftk2) $ rslice i n t
astSlice i n (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astSlice i n v
astSlice 0 n v | n == lengthAst v = v
astSlice _i n (Ast.AstReplicate _ stk@STKR{} v) =
  withSNat n $ \snat -> astReplicate snat stk v
astSlice i n (Ast.AstFromVector @y2 _ l) | STKR{} <- stensorKind @y2 =
  withSNat n $ \snat ->
    astFromVector snat $ V.take n $ V.drop i l
astSlice i n w@(Ast.AstAppend (u :: AstTensor AstMethodLet s (TKR2 (1 + k) r))
                              (v :: AstTensor AstMethodLet s (TKR2 (1 + k) r))) =
  let ulen = lengthAst u
  in if | i + n <= ulen -> astSlice @k i n u
        | i >= ulen -> astSlice @k (i - ulen) n v
        | otherwise -> Ast.AstSlice @k i n w  -- cheap iff fits in one
astSlice i n (Ast.AstGather (_ :$: sh') v (var ::: vars, ix)) =
  let ivar = AstIntVar var + fromIntegral i
      ix2 = substituteAstIxR  -- cheap subst, because ivar is tiny
              ivar var ix
  in astGatherR (n :$: sh') v (var ::: vars, ix2)
astSlice i n v = Ast.AstSlice i n v
{- TODO???
  AstSlice i n AstIotaR ->
    let u = Nested.rfromListPrimLinear (n :$: ZSR)
            $ map fromIntegral [i .. i + n - 1]
    in interpretAst env
       $ AstConcrete (FTKR (Nested.rshape u) FTKScalar) $ RepN u -}

astSliceS :: forall i n k sh s r.
             ( KnownNat i, KnownNat n, KnownNat k, KnownShS sh, TensorKind r
             , AstSpan s )
          => AstTensor AstMethodLet s (TKS2 (i + n + k ': sh) r)
          -> AstTensor AstMethodLet s (TKS2 (n ': sh) r)
astSliceS (AstConcrete (FTKS _ ftk2) t) =
  AstConcrete (FTKS knownShS ftk2) $ sslice (Proxy @i) (Proxy @n) t
astSliceS (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astSliceS @i @n v
astSliceS v | Just Refl <- sameNat (Proxy @i) (Proxy @0)
            , Just Refl <- sameNat (Proxy @k) (Proxy @0) = v
astSliceS (Ast.AstReplicate _ snat@STKS{} v) =
  astReplicate (SNat @n) snat v
astSliceS (Ast.AstFromVector @y2 _ l) | STKS{} <- stensorKind @y2 =
  astFromVector (SNat @n) $ V.take (valueOf @n) $ V.drop (valueOf @i) l
astSliceS w@(Ast.AstAppendS (u :: AstTensor AstMethodLet s (TKS2 (ulen : sh) r))
                            (v :: AstTensor AstMethodLet s (TKS2 (vlen : sh) r))) =
  case cmpNat (Proxy @(i + n)) (Proxy @ulen) of
    LTI -> astSliceS @i @n @(ulen - (i + n)) u
    EQI -> astSliceS @i @n @0 u
    GTI ->
      gcastWith (unsafeCoerceRefl :: vlen :~: i - ulen + n + k) $
      case cmpNat (Proxy @ulen) (Proxy @i) of
        LTI -> astSliceS @(i - ulen) @n @k v
        EQI -> astSliceS @0 @n @k v
        GTI -> Ast.AstSliceS @i w -- cheap iff fits in one
astSliceS (Ast.AstGatherS @_ @shn @shp v ((::$) @_ @sh21 (Const var) vars, ix))
                          | Dict <- slistKnown vars =
  let ivar = AstIntVar var + valueOf @i
      ix2 = substituteAstIxS  -- cheap subst, because ivar is tiny
              ivar var ix
      vars2 = Const var ::$ vars
  in astGatherS @(n : sh21) @shn @shp v (vars2, ix2)
astSliceS v = Ast.AstSliceS @i v
{- TODO: is this beneficial? for i==0 and for i/=0?
  AstSliceS @i @n AstIotaS ->
    let i = valueOf @i
        n = valueOf @n
    in interpretAst env
       $ AstConcrete (FTKS knownShS FTKScalar)
       $ RepN $ Nested.sfromListPrimLinear Nested.knownShS
       $ map fromIntegral [i :: Int .. i + n - 1]
-}

astReverse :: forall n s r. (KnownNat n, TensorKind r, AstSpan s)
           => AstTensor AstMethodLet s (TKR2 (1 + n) r)
           -> AstTensor AstMethodLet s (TKR2 (1 + n) r)
astReverse (AstConcrete ftk t) = AstConcrete ftk $ rreverse t
astReverse (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astReverse v
astReverse (Ast.AstReplicate snat stk v) = astReplicate snat stk v
astReverse (Ast.AstFromVector snat l) =
  astFromVector snat $ V.reverse l
astReverse (Ast.AstReverse v) = v
astReverse (Ast.AstGather sh@(k :$: _) v (var ::: vars, ix)) =
  let ivar = fromIntegral k - AstIntVar var
      ix2 = substituteAstIxR  -- cheap subst, because ivar is tiny
              ivar var ix
  in astGatherR sh v (var ::: vars, ix2)
astReverse v = Ast.AstReverse v

astReverseS :: forall n sh s r. (KnownNat n, KnownShS sh, TensorKind r, AstSpan s)
            => AstTensor AstMethodLet s (TKS2 (n ': sh) r)
            -> AstTensor AstMethodLet s (TKS2 (n ': sh) r)
astReverseS (AstConcrete ftk t) = AstConcrete ftk $ sreverse t
astReverseS (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astReverseS v
astReverseS (Ast.AstReplicate snat stk v) = astReplicate snat stk v
astReverseS (Ast.AstFromVector snat l) =
  astFromVector snat $ V.reverse l
astReverseS (Ast.AstReverseS v) = v
astReverseS (Ast.AstGatherS @shm @shn @shp v ((::$) @k (Const var) vars, ix)) =
  let ivar = valueOf @k - AstIntVar var
      ix2 = substituteAstIxS  -- cheap subst, because ivar is tiny
              ivar var ix
  in astGatherS @shm @shn @shp v (Const var ::$ vars, ix2)
astReverseS v = Ast.AstReverseS v

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astTransposeAsGather needs to be called in addition
-- if full simplification is required.
astTranspose :: forall n s r. (TensorKind r, KnownNat n, AstSpan s)
             => Permutation.PermR -> AstTensor AstMethodLet s (TKR2 n r)
             -> AstTensor AstMethodLet s (TKR2 n r)
astTranspose perm = \case
  t | null perm -> t
  Ast.AstLet var u v -> astLet var u (astTranspose perm v)
  AstN1R opCode u | not (isVar u) -> AstN1R opCode (astTranspose perm u)
  AstN2R opCode u v | not (isVar u && isVar v) ->
    AstN2R opCode (astTranspose perm u) (astTranspose perm v)
  Ast.AstR1R opCode u | not (isVar u) -> Ast.AstR1R opCode (astTranspose perm u)
  Ast.AstR2R opCode u v | not (isVar u && isVar v) ->
    Ast.AstR2R opCode (astTranspose perm u) (astTranspose perm v)
  Ast.AstSum snat stk v ->
    astSum snat stk $ astTranspose (0 : map succ perm) v
  Ast.AstScatter @_ @_ @p sh v (vars, ix) | length perm <= valueOf @p ->
    -- TODO: should the below be backpermute or permute?
    astScatter (Nested.Internal.Shape.shrPermutePrefix perm sh) v
               (vars, ixrPermutePrefix perm ix)
  Ast.AstTranspose perm2 t ->
    let perm2Matched =
          perm2
          ++ take (length perm - length perm2) (drop (length perm2) [0 ..])
        perm3 = normalizePermutationHack $ backpermutePrefixList perm perm2Matched
    in astTranspose perm3 t
      -- this rule can be disabled to test fusion of gathers
  -- Note that the following would be wrong, because transpose really
  -- changes the linearisation order, while reshape only modifies indexing:
  -- (perm, AstReshape sh v) -> astReshape (Nested.Internal.Shape.shrPermutePrefix perm sh) v
  Ast.AstGather @m sh v (vars, ix) | length perm <= valueOf @m ->
    -- TODO: should the below be backpermute or permute?
    astGatherR (Nested.Internal.Shape.shrPermutePrefix perm sh) v
               (Nested.Internal.Shape.listrPermutePrefix perm vars, ix)
  AstConcrete (FTKR sh x) t ->
    AstConcrete (FTKR (Nested.Internal.Shape.shrPermutePrefix perm sh) x)
    $ rtranspose perm t
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astTranspose perm v
  u -> Ast.AstTranspose perm u
    -- we don't go inside AstSumOfList, because they are usually long

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astTransposeAsGather needs to be called in addition
-- if full simplification is required.
astTransposeS :: forall perm sh s r.
                 ( PermC perm, KnownShS sh, Rank perm <= Rank sh
                 , TensorKind r, AstSpan s )
              => Permutation.Perm perm -> AstTensor AstMethodLet s (TKS2 sh r)
              -> AstTensor AstMethodLet s (TKS2 (Permutation.PermutePrefix perm sh) r)
astTransposeS perm t = case perm of
 Permutation.PNil -> t
 _ -> case t of
  Ast.AstLet var u v ->
    withKnownShS (shsPermutePrefix perm (knownShS @sh)) $
    astLet var u (astTransposeS perm v)
  AstN1S opCode u | not (isVar u) ->
    withKnownShS (shsPermutePrefix perm (knownShS @sh)) $
    AstN1S opCode (astTransposeS perm u)
  AstN2S opCode u v | not (isVar u && isVar v) ->
    withKnownShS (shsPermutePrefix perm (knownShS @sh)) $
    AstN2S opCode (astTransposeS perm u) (astTransposeS perm v)
  Ast.AstR1S opCode u | not (isVar u) ->
    withKnownShS (shsPermutePrefix perm (knownShS @sh)) $
    Ast.AstR1S opCode (astTransposeS perm u)
  Ast.AstR2S opCode u v | not (isVar u && isVar v) ->
    withKnownShS (shsPermutePrefix perm (knownShS @sh)) $
    Ast.AstR2S opCode (astTransposeS perm u) (astTransposeS perm v)
  Ast.AstSum snat@(SNat @n) _ v ->
    let zsuccP :: Permutation.Perm (0 : Permutation.MapSucc perm)
        zsuccP = Permutation.permShift1 perm
    in
      withKnownShS (shsPermutePrefix perm (knownShS @sh)) $
      gcastWith (unsafeCoerceRefl :: Rank (0 : Permutation.MapSucc perm)
                                     :~: 1 + Rank perm) $
      gcastWith (unsafeCoerceRefl
                 :: Permutation.PermutePrefix (0 : Permutation.MapSucc perm) (n : sh)
                    :~: n : Permutation.PermutePrefix perm sh) $
      trustMeThisIsAPermutation @(0 : Permutation.MapSucc perm) $
      astSum snat stensorKind $ astTransposeS zsuccP v
  Ast.AstScatterS @shm @shn @shp v (vars, ix)
    -- TODO: should the below be backpermute or permute?
    | gcompare (Permutation.permRank perm) (shsRank $ knownShS @shp) /= GGT ->
        withKnownShS (shsPermutePrefix perm (knownShS @shp)) $
        let ix2 :: AstIxS AstMethodLet (Permutation.PermutePrefix perm shp)
            ix2 = ixsPermutePrefix perm ix
        in gcastWith (unsafeCoerceRefl
                      :: Permutation.PermutePrefix perm shp ++ shn
                         :~: Permutation.PermutePrefix perm (shp ++ shn)) $
           astScatterS @shm @shn @(Permutation.PermutePrefix perm shp)
                       v (vars, ix2)
  Ast.AstTransposeS @_ @sh2 perm2 u ->  -- TODO: try to perform at type level
    let permV = Permutation.permToList' perm
        perm2V = Permutation.permToList' perm2
        perm2Matched =
          perm2V
          ++ take (length permV - length perm2V) (drop (length perm2V) [0 ..])
        perm3V = normalizePermutationHack $ backpermutePrefixList permV perm2Matched
    in Permutation.permFromList perm3V $ \(perm3 :: Permutation.Perm perm3) ->
      trustMeThisIsAPermutation @perm3 $
      gcastWith (unsafeCoerceRefl
                 :: Permutation.PermutePrefix perm3 sh2
                    :~: Permutation.PermutePrefix perm sh) $
      case compare (length perm3V)
                   (Nested.Internal.Shape.shsLength (knownShS @sh2)) of
        LT -> gcastWith (unsafeCoerceRefl
                         :: Compare (Rank perm3) (Rank sh2) :~: LT) $
              astTransposeS perm3 u
        EQ -> gcastWith (unsafeCoerceRefl
                         :: Compare (Rank perm3) (Rank sh2) :~: EQ) $
              astTransposeS perm3 u
        GT -> error "astTransposeS: GT"
  Ast.AstGatherS @shm @shn @shp v (vars, ix)
    -- TODO: should the below be backpermute or permute?
    | gcompare (Permutation.permRank perm) (shsRank $ knownShS @shm) /= GGT ->
        withKnownShS (shsPermutePrefix perm (knownShS @shm)) $
        let vars2 :: AstVarListS (Permutation.PermutePrefix perm shm)
            vars2 = Nested.Internal.Shape.listsPermutePrefix perm vars
        in gcastWith (unsafeCoerceRefl
                      :: Permutation.PermutePrefix perm shm ++ shn
                         :~: Permutation.PermutePrefix perm (shm ++ shn)) $
           astGatherS @(Permutation.PermutePrefix perm shm) @shn @shp
                      v (vars2, ix)
  AstConcrete (FTKS sh x) v ->
    let shPerm = Nested.Internal.Shape.shsPermutePrefix perm sh
    in withKnownShS shPerm $
       AstConcrete (FTKS shPerm x) $ stranspose perm v
  Ast.AstFromPrimal v ->
    withKnownShS (shsPermutePrefix perm (knownShS @sh)) $
    Ast.AstFromPrimal $ astTransposeS perm v
  u -> Ast.AstTransposeS @perm perm u  -- TODO

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astReshapeAsGather needs to be called in addition
-- if full simplification is required.
astReshape :: forall p m s r. (KnownNat p, KnownNat m, TensorKind r, AstSpan s)
           => IShR m -> AstTensor AstMethodLet s (TKR2 p r)
           -> AstTensor AstMethodLet s (TKR2 m r)
astReshape shOut = \case
  Ast.AstReplicate (SNat @k) STKR{} x
    | Just Refl <- sameNat (Proxy @k) (Proxy @1) ->
      astReshape shOut x
  Ast.AstLet var u v -> astLet var u (astReshape shOut v)
  AstN1R opCode u | not (isVar u) -> AstN1R opCode (astReshape shOut u)
  AstN2R opCode u v | not (isVar u && isVar v) ->
    AstN2R opCode (astReshape shOut u) (astReshape shOut v)
  Ast.AstR1R opCode u | not (isVar u) -> Ast.AstR1R opCode (astReshape shOut u)
  Ast.AstR2R opCode u v | not (isVar u && isVar v) ->
    Ast.AstR2R opCode (astReshape shOut u) (astReshape shOut v)
  Ast.AstFromVector @y2 snat l | Just Refl <- geq snat (SNat @1)
                               , STKR (SNat @n) _ <- stensorKind @y2
                               , Just Refl <- geq (SNat @(1 + n)) (SNat @p) ->
    astReshape shOut (l V.! 0)
  Ast.AstReshape _ v -> astReshape shOut v
  AstConcrete (FTKR _ x) t -> AstConcrete (FTKR shOut x)
                              $ rreshape shOut t
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astReshape shOut v
  v -> let shIn = shapeAst v
       in case sameNat (Proxy @p) (Proxy @m) of
         Just Refl -> if shIn == shOut
                      then v
                      else Ast.AstReshape shOut v
         _ -> Ast.AstReshape shOut v

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astReshapeAsGather needs to be called in addition
-- if full simplification is required.
astReshapeS :: forall sh sh2 r s.
               ( KnownShS sh, KnownShS sh2, Nested.Product sh ~ Nested.Product sh2
               , TensorKind r, AstSpan s )
            => AstTensor AstMethodLet s (TKS2 sh r)
            -> AstTensor AstMethodLet s (TKS2 sh2 r)
astReshapeS = \case
  Ast.AstReplicate (SNat @k) (STKS sh _) x
    | Just Refl <- sameNat (Proxy @k) (Proxy @1) ->
      withKnownShS sh $ astReshapeS x
  Ast.AstLet var u v -> astLet var u (astReshapeS @_ @sh2 v)
  AstN1S opCode u | not (isVar u) -> AstN1S opCode (astReshapeS @_ @sh2 u)
  AstN2S opCode u v | not (isVar u && isVar v) ->
    AstN2S opCode (astReshapeS @_ @sh2 u) (astReshapeS @_ @sh2 v)
  Ast.AstR1S opCode u | not (isVar u) ->
    Ast.AstR1S opCode (astReshapeS @_ @sh2 u)
  Ast.AstR2S opCode u v | not (isVar u && isVar v) ->
    Ast.AstR2S opCode (astReshapeS @_ @sh2 u) (astReshapeS @_ @sh2 v)
  Ast.AstFromVector @y2 snat l
   | Just Refl <- geq snat (SNat @1)
   , STKS sh3 _ <- stensorKind @y2
   , Just Refl <- testEquality (snat :$$ sh3) (knownShS @sh) ->
    withKnownShS sh3 $
    astReshapeS (l V.! 0)
  Ast.AstReshapeS v -> astReshapeS @_ @sh2 v
  AstConcrete (FTKS _ x) t -> AstConcrete (FTKS knownShS x)
                              $ sreshape t
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astReshapeS v
  v -> case sameShape @sh @sh2 of
         Just Refl -> v
         _ -> Ast.AstReshapeS v

astCast :: (GoodScalar r1, GoodScalar r2, RealFrac r1, RealFrac r2)
        => AstTensor ms s (TKScalar r1) -> AstTensor ms s (TKScalar r2)
astCast (AstConcrete FTKScalar t) = AstConcrete FTKScalar $ kcast t
astCast (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astCast v
astCast (Ast.AstCast v) = astCast v
astCast (Ast.AstFromIntegral v) = astFromIntegral v
astCast v = Ast.AstCast v

astCastR :: (KnownNat n, GoodScalar r1, GoodScalar r2, RealFrac r1, RealFrac r2)
        => AstTensor AstMethodLet s (TKR n r1) -> AstTensor AstMethodLet s (TKR n r2)
astCastR (AstConcrete (FTKR sh FTKScalar) t) =
  AstConcrete (FTKR sh FTKScalar) $ rcast t
astCastR (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astCastR v
astCastR (Ast.AstCastR v) = astCastR v
astCastR (Ast.AstFromIntegralR v) = astFromIntegralR v
astCastR v = Ast.AstCastR v

astCastS :: ( KnownShS sh, GoodScalar r1, GoodScalar r2, RealFrac r1
            , RealFrac r2 )
         => AstTensor AstMethodLet s (TKS sh r1)
         -> AstTensor AstMethodLet s (TKS sh r2)
astCastS (AstConcrete (FTKS sh FTKScalar) t) =
  AstConcrete (FTKS sh FTKScalar) $ scast t
astCastS (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astCastS v
astCastS (Ast.AstCastS v) = astCastS v
astCastS (Ast.AstFromIntegralS v) = astFromIntegralS v
astCastS v = Ast.AstCastS v

astFromIntegral :: (GoodScalar r1, GoodScalar r2, Integral r1)
                => AstTensor ms PrimalSpan (TKScalar r1)
                -> AstTensor ms PrimalSpan (TKScalar r2)
astFromIntegral (AstConcrete FTKScalar t) = AstConcrete FTKScalar $ kfromIntegral t
astFromIntegral (Ast.AstFromIntegral v) = astFromIntegral v
astFromIntegral v = Ast.AstFromIntegral v

astFromIntegralR :: (KnownNat n, GoodScalar r1, GoodScalar r2, Integral r1)
                => AstTensor AstMethodLet PrimalSpan (TKR n r1)
                -> AstTensor AstMethodLet PrimalSpan (TKR n r2)
astFromIntegralR (AstConcrete (FTKR sh FTKScalar) t) = AstConcrete (FTKR sh FTKScalar) $ rfromIntegral t
astFromIntegralR (Ast.AstFromIntegralR v) = astFromIntegralR v
astFromIntegralR v = Ast.AstFromIntegralR v

astFromIntegralS :: (KnownShS sh, GoodScalar r1, GoodScalar r2, Integral r1)
                 => AstTensor AstMethodLet PrimalSpan (TKS sh r1)
                 -> AstTensor AstMethodLet PrimalSpan (TKS sh r2)
astFromIntegralS (AstConcrete (FTKS sh FTKScalar) t) =
  AstConcrete (FTKS sh FTKScalar) $ sfromIntegral t
astFromIntegralS (Ast.AstFromIntegralS v) = astFromIntegralS v
astFromIntegralS v = Ast.AstFromIntegralS v

astProject1
  :: forall x z s. (TensorKind x, TensorKind z, AstSpan s)
  => AstTensor AstMethodLet s (TKProduct x z) -> AstTensor AstMethodLet s x
astProject1 u = case u of
  Ast.AstPair x _z -> x
  Ast.AstLet var t v -> Ast.AstLet var t (astProject1 v)
  Ast.AstLetHVectorIn vars l v -> astLetHVectorIn vars l (astProject1 v)
-- TODO: Ast.AstConcrete u1 -> Ast.AstConcrete $ tproject1 u1
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

astRFromS :: forall sh s r. (TensorKind r, KnownShS sh)
          => AstTensor AstMethodLet s (TKS2 sh r)
          -> AstTensor AstMethodLet s (TKR2 (Rank sh) r)
astRFromS (Ast.AstSFromR v) = v  -- no information lost, so no checks
astRFromS v = Ast.AstRFromS v

-- We are pushing conversions to shaped tensors down, into concrete values
-- and towards variables, which we convert from shaped to ranked and mixed
-- so that the conversions cancel out. Consequently, the conversions away
-- from shaped are pushed up.
astSFromR :: forall sh s r.
             (TensorKind r, KnownShS sh, KnownNat (Rank sh), AstSpan s)
          => AstTensor AstMethodLet s (TKR2 (Rank sh) r)
          -> AstTensor AstMethodLet s (TKS2 sh r)
astSFromR a0 = case a0 of
  Ast.AstProject1{} -> Ast.AstSFromR a0  -- TODO: convert arbitrary tensor?
  Ast.AstProject2{} -> Ast.AstSFromR a0
  Ast.AstApply{} -> Ast.AstSFromR a0
  Ast.AstVar{} -> Ast.AstSFromR a0
  Ast.AstPrimalPart a -> astPrimalPart $ astSFromR a
  Ast.AstDualPart a -> astDualPart $ astSFromR a
  Ast.AstFromPrimal a -> Ast.AstFromPrimal $ astSFromR a
  Ast.AstD u u' -> Ast.AstD (astSFromR u) (astSFromR u')
  Ast.AstCond b v w -> astCond b (astSFromR v) (astSFromR w)
  Ast.AstFromVector @y2 snat@SNat l
   | STKR{} <- stensorKind @y2 -> case knownShS @sh of
    (:$$) @_ @rest snat2 rest | Just Refl <- sameNat snat snat2
                              , SNat <- shsRank rest ->
      withKnownShS rest $
      astFromVector snat (V.map (astSFromR @rest) l)
    _ -> error "astSFromR: impossible shape"
  Ast.AstSum snat@SNat (STKR _ x) a ->
    astSum snat (STKS knownShS x) (astSFromR a)
  Ast.AstReplicate snat@SNat (STKR SNat x) a -> case knownShS @sh of
    (:$$) @_ @rest snat2 rest | Just Refl <- sameNat snat snat2 ->
      withKnownShS rest $
      astReplicate snat (STKS rest x) (astSFromR @rest a)
    _ -> error "astSFromR: impossible shape"
  Ast.AstBuild1 snat@(SNat @k) (var, v) -> case ftkAst v of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh2 :: ShS sh2) ->
        gcastWith (unsafeCoerceRefl :: k ': sh2 :~: sh) $
        withKnownShS sh2 $
        Ast.AstBuild1 snat (var, astSFromR @sh2 v)
  Ast.AstLet var u v ->  astLet var u (astSFromR v)
  AstConcrete (FTKR _ x) v -> AstConcrete (FTKS knownShS x) (sfromR v)

  AstSumOfList (STKR _ x) args ->
    astSumOfList (STKS knownShS x) (map astSFromR args)

  AstN1R{} -> Ast.AstSFromR a0
  AstN2R{} -> Ast.AstSFromR a0
  Ast.AstR1R{} -> Ast.AstSFromR a0
  Ast.AstR2R{} -> Ast.AstSFromR a0
  Ast.AstI2R{} -> Ast.AstSFromR a0
  Ast.AstFloorR{} -> Ast.AstSFromR a0
  Ast.AstFromIntegralR{} -> Ast.AstSFromR a0
  Ast.AstCastR{} -> Ast.AstSFromR a0
  Ast.AstMinIndexR{} -> Ast.AstSFromR a0
  Ast.AstMaxIndexR{} -> Ast.AstSFromR a0
  Ast.AstIotaR{} -> Ast.AstSFromR a0
  Ast.AstIndex{} -> Ast.AstSFromR a0
  Ast.AstScatter{} -> Ast.AstSFromR a0
  Ast.AstAppend{} -> Ast.AstSFromR a0
  Ast.AstSlice{} -> Ast.AstSFromR a0
  Ast.AstReverse{} -> Ast.AstSFromR a0
  Ast.AstTranspose{} -> Ast.AstSFromR a0
  Ast.AstReshape{} -> Ast.AstSFromR a0
  Ast.AstGather{} -> Ast.AstSFromR a0
  Ast.AstZipR{} -> Ast.AstSFromR a0

  Ast.AstRFromS @sh1 v ->
    case sameShape @sh1 @sh of
      Just Refl -> v
      _ -> error "astSFromR: different ranks in SFromR(RFromS)"

  -- These should not appear here unless via wacky tests.
  Ast.AstReplicate0NR{} -> Ast.AstSFromR a0
  Ast.AstSum0R{} -> Ast.AstSFromR a0
  Ast.AstDot0R{} -> Ast.AstSFromR a0
  Ast.AstDot1InR{} -> Ast.AstSFromR a0
  Ast.AstMatvecmulR{} -> Ast.AstSFromR a0
  Ast.AstMatmul2R{} -> Ast.AstSFromR a0

  Ast.AstProjectR{} -> Ast.AstSFromR a0
  Ast.AstLetHVectorIn{} -> Ast.AstSFromR a0

-- TODO
astSFromX :: forall sh sh' s r.
             (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', TensorKind r)
          => AstTensor AstMethodLet s (TKX2 sh' r)
          -> AstTensor AstMethodLet s (TKS2 sh r)
astSFromX (AstConcrete ftk t) = case ftk of
  FTKX _ x ->
    let u = sfromX t
    in AstConcrete (FTKS knownShS x) u
astSFromX (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astSFromX v
astSFromX (Ast.AstXFromS @sh1 v) =
  case sameShape @sh1 @sh of
    Just Refl -> v
    _ -> error "astSFromX: different shapes in SFromX(XFromS)"
astSFromX v = Ast.AstSFromX v

astXFromS :: forall sh sh' s r.
             (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', TensorKind r)
          => AstTensor AstMethodLet s (TKS2 sh r)
          -> AstTensor AstMethodLet s (TKX2 sh' r)
-- impossible, shapes may differ: astXFromS (Ast.AstSFromX v) = v
astXFromS v = Ast.AstXFromS v

astXNestR
  :: forall sh1 m x ms s.
     (TensorKind x, KnownShX sh1, KnownNat m, AstSpan s)
  => AstTensor ms s (TKX2 (sh1 ++ Replicate m Nothing) x)
  -> AstTensor ms s (TKX2 sh1 (TKR2 m x))
astXNestR t = case t of
  Ast.AstLet var u2 d2 ->  -- TODO: good idea?
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    astLet var u2 (astXNestR d2)
  Ast.AstFromPrimal u ->
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    Ast.AstFromPrimal $ astXNestR u
  Ast.AstCond b v1 v2 ->
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    Ast.AstCond b (astXNestR v1) (astXNestR v2)  -- TODO: ??
-- TODO: when sh agrees:  Ast.AstUnNestS u -> u
  _ -> Ast.AstXNestR t

astXNestS
  :: forall sh1 sh2 x ms s.
     (TensorKind x, KnownShX sh1, KnownShS sh2, AstSpan s)
  => AstTensor ms s (TKX2 (sh1 ++ MapJust sh2) x)
  -> AstTensor ms s (TKX2 sh1 (TKS2 sh2 x))
astXNestS t = case t of
  Ast.AstLet var u2 d2 ->  -- TODO: good idea?
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    astLet var u2 (astXNestS d2)
  Ast.AstFromPrimal u ->
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    Ast.AstFromPrimal $ astXNestS u
  Ast.AstCond b v1 v2 ->
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    Ast.AstCond b (astXNestS v1) (astXNestS v2)  -- TODO: ??
  _ -> Ast.AstXNestS t

astXNest
  :: forall sh1 sh2 x ms s.
     (TensorKind x, KnownShX sh1, KnownShX sh2, AstSpan s)
  => AstTensor ms s (TKX2 (sh1 ++ sh2) x)
  -> AstTensor ms s (TKX2 sh1 (TKX2 sh2 x))
astXNest t = case t of
  Ast.AstLet var u2 d2 ->  -- TODO: good idea?
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    astLet var u2 (astXNest d2)
  Ast.AstFromPrimal u ->
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    Ast.AstFromPrimal $ astXNest u
  Ast.AstCond b v1 v2 ->
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    Ast.AstCond b (astXNest v1) (astXNest v2)  -- TODO: ??
  _ -> Ast.AstXNest t

astXUnNestR
  :: forall sh1 m x ms s.
     (TensorKind x, KnownShX sh1, KnownNat m, AstSpan s)
  => AstTensor ms s (TKX2 sh1 (TKR2 m x))
  -> AstTensor ms s (TKX2 (sh1 ++ Replicate m Nothing) x)
astXUnNestR t = case t of
  Ast.AstLet var u2 d2 ->  -- TODO: good idea?
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    astLet var u2 (astXUnNestR d2)
  Ast.AstFromPrimal u ->
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    Ast.AstFromPrimal $ astXUnNestR u
  Ast.AstCond b v1 v2 ->
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    Ast.AstCond b (astXUnNestR v1) (astXUnNestR v2)  -- TODO: ??
--  Ast.AstNestS u -> u
  _ -> Ast.AstXUnNestR t

astXUnNestS
  :: forall sh1 sh2 x ms s.
     (TensorKind x, KnownShX sh1, KnownShS sh2, AstSpan s)
  => AstTensor ms s (TKX2 sh1 (TKS2 sh2 x))
  -> AstTensor ms s (TKX2 (sh1 ++ MapJust sh2) x)
astXUnNestS t = case t of
  Ast.AstLet var u2 d2 ->  -- TODO: good idea?
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    astLet var u2 (astXUnNestS d2)
  Ast.AstFromPrimal u ->
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    Ast.AstFromPrimal $ astXUnNestS u
  Ast.AstCond b v1 v2 ->
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    Ast.AstCond b (astXUnNestS v1) (astXUnNestS v2)  -- TODO: ??
--  Ast.AstNestS u -> u
  _ -> Ast.AstXUnNestS t

astXUnNest
  :: forall sh1 sh2 x ms s.
     (TensorKind x, KnownShX sh1, KnownShX sh2, AstSpan s)
  => AstTensor ms s (TKX2 sh1 (TKX2 sh2 x))
  -> AstTensor ms s (TKX2 (sh1 ++ sh2) x)
astXUnNest t = case t of
  Ast.AstLet var u2 d2 ->  -- TODO: good idea?
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    astLet var u2 (astXUnNest d2)
  Ast.AstFromPrimal u ->
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    Ast.AstFromPrimal $ astXUnNest u
  Ast.AstCond b v1 v2 ->
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    Ast.AstCond b (astXUnNest v1) (astXUnNest v2)  -- TODO: ??
--  Ast.AstNestS u -> u
  _ -> Ast.AstXUnNest t

astPrimalPart :: TensorKind y
              => AstTensor AstMethodLet FullSpan y
              -> AstTensor AstMethodLet PrimalSpan y
astPrimalPart t = case t of
  Ast.AstPair t1 t2 -> astPair (astPrimalPart t1) (astPrimalPart t2)
  Ast.AstProject1 v -> astProject1 (astPrimalPart v)
  Ast.AstProject2 v -> astProject2 (astPrimalPart v)
  Ast.AstApply v ll -> astHApply v (astPrimalPart ll)
  Ast.AstVar{} -> Ast.AstPrimalPart t  -- the only normal form
  Ast.AstFromPrimal v -> v
  Ast.AstD u _ -> u
  Ast.AstCond b a2 a3 -> astCond b (astPrimalPart a2) (astPrimalPart a3)
  Ast.AstFromVector snat l -> astFromVector snat (V.map astPrimalPart l)
  Ast.AstSum snat stk v | Dict <- lemTensorKindOfBuild snat stk ->
    astSum snat stk (astPrimalPart v)
  Ast.AstReplicate snat stk v | Dict <- lemTensorKindOfSTK stk ->
    astReplicate snat stk (astPrimalPart v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, astPrimalPart v)
  Ast.AstLet var u v -> astLet var u (astPrimalPart v)
  Ast.AstMapAccumRDer @_ @_ @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs) ->
      Ast.AstMapAccumRDer k accShs bShs eShs f df rf
                          (astPrimalPart acc0) (astPrimalPart es)
  Ast.AstMapAccumLDer @_ @_ @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs) ->
      Ast.AstMapAccumRDer k accShs bShs eShs f df rf
                          (astPrimalPart acc0) (astPrimalPart es)

  AstSumOfList stk args -> astSumOfList stk (map astPrimalPart args)

  AstN1 opCode u -> AstN1 opCode (astPrimalPart u)
  AstN2 opCode u v -> AstN2 opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstR1 opCode u -> Ast.AstR1 opCode (astPrimalPart u)
  Ast.AstR2 opCode u v -> Ast.AstR2 opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2 opCode u v -> Ast.AstI2 opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstCast v -> astCast $ astPrimalPart v

  AstN1R opCode u -> AstN1R opCode (astPrimalPart u)
  AstN2R opCode u v -> AstN2R opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstR1R opCode u -> Ast.AstR1R opCode (astPrimalPart u)
  Ast.AstR2R opCode u v -> Ast.AstR2R opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2R opCode u v -> Ast.AstI2R opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstCastR v -> astCastR $ astPrimalPart v
  Ast.AstIndex v ix -> astIndexR (astPrimalPart v) ix
  Ast.AstScatter sh v (var, ix) -> astScatter sh (astPrimalPart v) (var, ix)
  Ast.AstAppend x y -> astAppend (astPrimalPart x) (astPrimalPart y)
  Ast.AstSlice i k v -> astSlice i k (astPrimalPart v)
  Ast.AstReverse v -> astReverse (astPrimalPart v)
  Ast.AstTranspose perm v -> astTranspose perm (astPrimalPart v)
  Ast.AstReshape sh v -> astReshape sh (astPrimalPart v)
  Ast.AstGather sh v (vars, ix) -> astGatherR sh (astPrimalPart v) (vars, ix)
  Ast.AstZipR v -> Ast.AstZipR (astPrimalPart v)
  Ast.AstUnzipR v -> Ast.AstUnzipR (astPrimalPart v)

  Ast.AstFromScalar u -> astFromScalar $ astPrimalPart u
  Ast.AstToScalar u -> Ast.AstToScalar $ astPrimalPart u
  AstN1S opCode u -> AstN1S opCode (astPrimalPart u)
  AstN2S opCode u v -> AstN2S opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astPrimalPart u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (astPrimalPart u)
                                             (astPrimalPart v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (astPrimalPart u)
                                             (astPrimalPart v)
  Ast.AstCastS v -> astCastS $ astPrimalPart v
  Ast.AstIndexS @shm @shn v ix ->
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    astIndexS (astPrimalPart v) ix
  Ast.AstScatterS @shm @shn @shp v (var, ix) ->
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    astScatterS @shm @shn @shp (astPrimalPart v) (var, ix)
  Ast.AstAppendS x y -> astAppendS (astPrimalPart x) (astPrimalPart y)
  Ast.AstSliceS @i v -> astSliceS @i (astPrimalPart v)
  Ast.AstReverseS v -> astReverseS (astPrimalPart v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astPrimalPart v)
  Ast.AstReshapeS v -> astReshapeS (astPrimalPart v)
  Ast.AstGatherS @shm @shn @shp v (vars, ix) ->
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    astGatherS @shm @shn @shp (astPrimalPart v) (vars, ix)
  Ast.AstZipS v -> Ast.AstZipS (astPrimalPart v)
  Ast.AstUnzipS v -> Ast.AstUnzipS (astPrimalPart v)

  Ast.AstRFromS v -> astRFromS $ astPrimalPart v
  -- These conversions need to stay down.
  Ast.AstSFromR{} -> Ast.AstPrimalPart t
  Ast.AstSFromX{} -> Ast.AstPrimalPart t
  Ast.AstXFromS v -> astXFromS $ astPrimalPart v

  Ast.AstXNestR @sh1 @m v ->
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    astXNestR $ astPrimalPart v
  Ast.AstXNestS @sh1 @sh2 v ->
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    astXNestS $ astPrimalPart v
  Ast.AstXNest @sh1 @sh2 v ->
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    astXNest $ astPrimalPart v
  Ast.AstXUnNestR v -> astXUnNestR $ astPrimalPart v
  Ast.AstXUnNestS v -> astXUnNestS $ astPrimalPart v
  Ast.AstXUnNest v -> astXUnNest $ astPrimalPart v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstReplicate0NR{} -> Ast.AstPrimalPart t
  Ast.AstSum0R{} -> Ast.AstPrimalPart t
  Ast.AstDot0R{} -> Ast.AstPrimalPart t
  Ast.AstDot1InR{} -> Ast.AstPrimalPart t
  Ast.AstMatvecmulR{} -> Ast.AstPrimalPart t
  Ast.AstMatmul2R{} -> Ast.AstPrimalPart t
  Ast.AstReplicate0NS{} -> Ast.AstPrimalPart t
  Ast.AstSum0S{} -> Ast.AstPrimalPart t
  Ast.AstDot0S{} -> Ast.AstPrimalPart t
  Ast.AstDot1InS{} -> Ast.AstPrimalPart t
  Ast.AstMatvecmulS{} -> Ast.AstPrimalPart t
  Ast.AstMatmul2S{} -> Ast.AstPrimalPart t

  Ast.AstMkHVector{} -> Ast.AstPrimalPart t  -- TODO
  Ast.AstProjectR l p -> astProjectR (astPrimalPart l) p
  Ast.AstLetHVectorIn vars l v -> astLetHVectorIn vars l (astPrimalPart v)
  Ast.AstProjectS l p -> astProjectS (astPrimalPart l) p

-- Note how this can't be pushed down, say, multiplication, because it
-- multiplies the dual part by the primal part. Addition is fine, though.
astDualPart :: TensorKind y
            => AstTensor AstMethodLet FullSpan y
            -> AstTensor AstMethodLet DualSpan y
astDualPart t = case t of
  Ast.AstPair t1 t2 -> astPair (astDualPart t1) (astDualPart t2)
  Ast.AstProject1 v -> astProject1 (astDualPart v)
  Ast.AstProject2 v -> astProject2 (astDualPart v)
  Ast.AstApply v ll -> astHApply v (astDualPart ll)
  Ast.AstVar{} -> Ast.AstDualPart t
  Ast.AstFromPrimal{}  -> Ast.AstDualPart t  -- this equals nil (not primal 0)
  Ast.AstD _ u' -> u'
  Ast.AstCond b a2 a3 -> astCond b (astDualPart a2) (astDualPart a3)
  Ast.AstFromVector snat l -> astFromVector snat (V.map astDualPart l)
  Ast.AstSum snat stk v | Dict <- lemTensorKindOfBuild snat stk ->
    astSum snat stk (astDualPart v)
  Ast.AstReplicate snat stk v | Dict <- lemTensorKindOfSTK stk ->
    astReplicate snat stk (astDualPart v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, astDualPart v)
  Ast.AstLet var u v -> astLet var u (astDualPart v)
  Ast.AstMapAccumRDer @_ @_ @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs) ->
      Ast.AstMapAccumRDer k accShs bShs eShs f df rf
                          (astDualPart acc0) (astDualPart es)
  Ast.AstMapAccumLDer @_ @_ @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs) ->
      Ast.AstMapAccumRDer k accShs bShs eShs f df rf
                          (astDualPart acc0) (astDualPart es)

  AstSumOfList stk args -> astSumOfList stk (map astDualPart args)

  AstN1{} -> Ast.AstDualPart t  -- stuck; the ops are not defined on dual part
  AstN2{} -> Ast.AstDualPart t  -- stuck; the ops are not defined on dual part
  Ast.AstR1{} -> Ast.AstDualPart t
  Ast.AstR2{} -> Ast.AstDualPart t
  Ast.AstI2{} -> Ast.AstDualPart t
  Ast.AstCast v -> astCast $ astDualPart v

  AstN1R{} -> Ast.AstDualPart t  -- stuck; the ops are not defined on dual part
  AstN2R{} -> Ast.AstDualPart t  -- stuck; the ops are not defined on dual part
  Ast.AstR1R{} -> Ast.AstDualPart t
  Ast.AstR2R{} -> Ast.AstDualPart t
  Ast.AstI2R{} -> Ast.AstDualPart t
  Ast.AstCastR v -> astCastR $ astDualPart v
  Ast.AstIndex v ix -> astIndexR (astDualPart v) ix
  Ast.AstScatter sh v (var, ix) -> astScatter sh (astDualPart v) (var, ix)
  Ast.AstAppend x y -> astAppend (astDualPart x) (astDualPart y)
  Ast.AstSlice i k v -> astSlice i k (astDualPart v)
  Ast.AstReverse v -> astReverse (astDualPart v)
  Ast.AstTranspose perm v -> astTranspose perm (astDualPart v)
  Ast.AstReshape sh v -> astReshape sh (astDualPart v)
  Ast.AstGather sh v (vars, ix) -> astGatherR sh (astDualPart v) (vars, ix)
  Ast.AstZipR v -> Ast.AstZipR (astDualPart v)
  Ast.AstUnzipR v -> Ast.AstUnzipR (astDualPart v)

  Ast.AstFromScalar u -> astFromScalar $ astDualPart u
  Ast.AstToScalar u -> Ast.AstToScalar $ astDualPart u
  AstN1S{} -> Ast.AstDualPart t
  AstN2S{} -> Ast.AstDualPart t
  Ast.AstR1S{} -> Ast.AstDualPart t
  Ast.AstR2S{} -> Ast.AstDualPart t
  Ast.AstI2S{} -> Ast.AstDualPart t
  Ast.AstCastS v -> astCastS $ astDualPart v
  Ast.AstIndexS @shm @shn v ix ->
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    astIndexS (astDualPart v) ix
  Ast.AstScatterS @shm @shn @shp v (var, ix) ->
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    astScatterS @shm @shn @shp (astDualPart v) (var, ix)
  Ast.AstAppendS x y -> astAppendS (astDualPart x) (astDualPart y)
  Ast.AstSliceS @i v -> astSliceS @i (astDualPart v)
  Ast.AstReverseS v -> astReverseS (astDualPart v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astDualPart v)
  Ast.AstReshapeS v -> astReshapeS (astDualPart v)
  Ast.AstGatherS @shm @shn @shp v (vars, ix) ->
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    astGatherS @shm @shn @shp (astDualPart v) (vars, ix)
  Ast.AstZipS v -> Ast.AstZipS (astDualPart v)
  Ast.AstUnzipS v -> Ast.AstUnzipS (astDualPart v)

  Ast.AstRFromS v -> astRFromS $ astDualPart v
   -- These conversions need to stay down.
  Ast.AstSFromR {} -> Ast.AstDualPart t
  Ast.AstSFromX{} -> Ast.AstDualPart t
  Ast.AstXFromS v -> astXFromS $ astDualPart v

  Ast.AstXNestR @sh1 @m v ->
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    astXNestR $ astDualPart v
  Ast.AstXNestS @sh1 @sh2 v ->
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    astXNestS $ astDualPart v
  Ast.AstXNest @sh1 @sh2 v ->
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    astXNest $ astDualPart v
  Ast.AstXUnNestR v -> astXUnNestR $ astDualPart v
  Ast.AstXUnNestS v -> astXUnNestS $ astDualPart v
  Ast.AstXUnNest v -> astXUnNest $ astDualPart v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstReplicate0NR{} -> Ast.AstDualPart t
  Ast.AstSum0R{} -> Ast.AstDualPart t
  Ast.AstDot0R{} -> Ast.AstDualPart t
  Ast.AstDot1InR{} -> Ast.AstDualPart t
  Ast.AstMatvecmulR{} -> Ast.AstDualPart t
  Ast.AstMatmul2R{} -> Ast.AstDualPart t
  Ast.AstReplicate0NS{} -> Ast.AstDualPart t
  Ast.AstSum0S{} -> Ast.AstDualPart t
  Ast.AstDot0S{} -> Ast.AstDualPart t
  Ast.AstDot1InS{} -> Ast.AstDualPart t
  Ast.AstMatvecmulS{} -> Ast.AstDualPart t
  Ast.AstMatmul2S{} -> Ast.AstDualPart t

  Ast.AstMkHVector{} -> Ast.AstDualPart t  -- TODO
  Ast.AstProjectR l p -> astProjectR (astDualPart l) p
  Ast.AstLetHVectorIn vars l v -> astLetHVectorIn vars l (astDualPart v)
  Ast.AstProjectS l p -> astProjectS (astDualPart l) p

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
          fRanked (mkAstVarName varId) (astRFromS @sh3 @_ @(TKScalar r3) (astReplicate0NS 0)) acc
  DynamicShapedDummy @r4 @sh4 _ _
    | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
    , Just Refl <- sameShape @sh3 @sh4
    , Just Refl <- testEquality (typeRep @r3) (typeRep @r4) ->
        fShaped @sh4 @r4 (mkAstVarName varId) (astReplicate0NS 0) acc
  _ -> error $ "mapRankedShaped: corrupted arguments"
               `showFailure`
               ( vd, typeRep @ty, typeRep @r3, knownShS @sh3
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
        STKScalar _ -> Ast.AstToScalar $ astProjectS l i
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
        STKScalar _ -> Ast.AstToScalar $ astPrimalPart $ astProjectS l i
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
        STKScalar _ -> Ast.AstToScalar $ astDualPart $ astProjectS l i
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
                     , SNat <- shsRank (knownShS @sh3) =
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

astFromScalar :: (GoodScalar r, AstSpan s)
              => AstTensor ms s (TKScalar r) -> AstTensor ms s (TKS '[] r)
astFromScalar t = case t of
  Ast.AstToScalar u -> u
  Ast.AstCond b a2 a3 -> Ast.AstCond b (astFromScalar a2) (astFromScalar a3)
  AstConcrete FTKScalar (RepN v) ->
    AstConcrete (FTKS ZSS FTKScalar) $ sscalar v
  AstN1 opCode u -> AstN1S opCode (astFromScalar u)
  AstN2 opCode u v -> AstN2S opCode (astFromScalar u) (astFromScalar v)
-- TODO:  Ast.AstR1 opCode u -> Ast.AstR1S opCode (astFromScalar u)
-- TODO:  Ast.AstR2 opCode u v -> Ast.AstR2S opCode (astFromScalar u) (astFromScalar v)
  Ast.AstI2 opCode u v | Just Refl <- isTensorInt t ->
    Ast.AstI2S opCode (astFromScalar u) (astFromScalar v)
  AstSumOfList _ args -> AstSumOfList stensorKind $ map astFromScalar args
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astFromScalar v
  _ -> Ast.AstFromScalar t


-- * The expansion (e.g., into gather expressions) bottom-up pass

expandAstInt :: AstInt AstMethodLet -> AstInt AstMethodLet
expandAstInt = expandAst

expandAstIxR :: AstIxR AstMethodLet n -> AstIxR AstMethodLet n
expandAstIxR = fmap expandAstInt

expandAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
expandAstIxS = fmap expandAstInt

expandAst
  :: forall s y. (AstSpan s, TensorKind y)
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
expandAst t = case t of
  Ast.AstPair t1 t2 -> astPair (expandAst t1) (expandAst t2)
  Ast.AstProject1 v -> astProject1 (expandAst v)
  Ast.AstProject2 v -> astProject2 (expandAst v)
  Ast.AstApply v ll -> astHApply (expandAstHFun v) (expandAst ll)
  Ast.AstVar{} -> t
  Ast.AstPrimalPart v -> astPrimalPart (expandAst v)
  Ast.AstDualPart v -> astDualPart (expandAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (expandAst v)
  Ast.AstD u u' -> Ast.AstD (expandAst u) (expandAst u')
  Ast.AstCond b a2 a3 ->
    astCond (expandAstBool b) (expandAst a2) (expandAst a3)
  Ast.AstFromVector snat l -> astFromVector snat (V.map expandAst l)
  Ast.AstSum snat stk v | Dict <- lemTensorKindOfBuild snat stk ->
    astSum snat stk (expandAst v)
  Ast.AstReplicate snat stk v | Dict <- lemTensorKindOfSTK stk ->
    astReplicate snat stk (expandAst v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, expandAst v)
  Ast.AstLet var u v -> astLet var (expandAst u) (expandAst v)
  AstConcrete{} -> t
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

  AstSumOfList stk args ->
    case isTensorInt t of
      Just Refl -> foldr1 contractAstPlusOp (map expandAst args)
      _ -> astSumOfList stk (map expandAst args)

  AstN1 opCode u ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp1 opCode (expandAst u)
      _ -> AstN1 opCode (expandAst u)
  AstN2 opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp2 opCode (expandAst u) (expandAst v)
      _ -> {- TODO: case opCode of
        TimesOp | Just Refl <- sameNat (Proxy @n) (Proxy @3) ->
          AstN2R opCode (simplifyAst u) (simplifyAst v)
            -- TODO: a workaround for interpretMatmul2 not yet generalized
            -- to gathers (and moved from AstInterpret here, ideally)
        _ -> -} AstN2 opCode (expandAst u) (expandAst v)
  Ast.AstR1 opCode u -> Ast.AstR1 opCode (expandAst u)
  Ast.AstR2 opCode u v -> Ast.AstR2 opCode (expandAst u) (expandAst v)
  Ast.AstI2 opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstIntegralOp2 opCode (expandAst u) (expandAst v)
      _ -> Ast.AstI2 opCode (expandAst u) (expandAst v)
  Ast.AstFloor a -> Ast.AstFloor (expandAst a)
  Ast.AstFromIntegral v -> astFromIntegral $ expandAst v
  Ast.AstCast v -> astCast $ expandAst v

  AstN1R opCode u -> AstN1R opCode (expandAst u)
  AstN2R opCode u v -> AstN2R opCode (expandAst u) (expandAst v)
  Ast.AstR1R opCode u -> Ast.AstR1R opCode (expandAst u)
  Ast.AstR2R opCode u v -> Ast.AstR2R opCode (expandAst u) (expandAst v)
  Ast.AstI2R opCode u v -> Ast.AstI2R opCode (expandAst u) (expandAst v)
  Ast.AstFloorR a -> Ast.AstFloorR (expandAst a)
  Ast.AstFromIntegralR v -> astFromIntegralR $ expandAst v
  Ast.AstCastR v -> astCastR $ expandAst v
  Ast.AstMinIndexR a -> Ast.AstMinIndexR (expandAst a)
  Ast.AstMaxIndexR a -> Ast.AstMaxIndexR (expandAst a)
  Ast.AstIotaR{} -> t
  Ast.AstIndex v ix -> astIndexKnobsR (defaultKnobs {knobExpand = True})
                                      (expandAst v)
                                      (expandAstIxR ix)
  Ast.AstScatter sh v (var, ix) ->
    astScatter sh (expandAst v) (var, expandAstIxR ix)
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
    AstSumOfList{} -> t  -- normal form
    AstN1R _ w | isVar w -> t  -- normal form
    AstN2R _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstR1R _ w | isVar w -> t  -- normal form
    Ast.AstR2R _ x y | isVar x && isVar y -> t  -- normal form
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
    AstSumOfList{} -> t  -- normal form
    AstN1R _ w | isVar w -> t  -- normal form
    AstN2R _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstR1R _ w | isVar w -> t  -- normal form
    Ast.AstR2R _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstScatter{} -> t  -- normal form
    _ ->  -- not nf, let's express all as a gather
      astReshapeAsGather (defaultKnobs {knobExpand = True})
                         sh
                         (expandAst v)
        -- this is expensive but the only way to guarantee full simplification
  Ast.AstGather sh v (vars, ix) ->
    astGatherKnobsR (defaultKnobs {knobExpand = True})
                    sh (expandAst v) (vars, expandAstIxR ix)
  Ast.AstZipR v -> Ast.AstZipR (expandAst v)
  Ast.AstUnzipR v -> Ast.AstUnzipR (expandAst v)

  Ast.AstFromScalar u -> astFromScalar $ expandAst u
  Ast.AstToScalar u -> Ast.AstToScalar $ expandAst u
  AstN1S opCode u -> AstN1S opCode (expandAst u)
  AstN2S opCode u v -> AstN2S opCode (expandAst u) (expandAst v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (expandAst u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (expandAst u) (expandAst v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (expandAst u) (expandAst v)
  Ast.AstFloorS a -> Ast.AstFloorS (expandAst a)
  Ast.AstFromIntegralS v -> astFromIntegralS $ expandAst v
  Ast.AstCastS v -> astCastS $ expandAst v
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (expandAst a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (expandAst a)
  Ast.AstIotaS -> t
  Ast.AstIndexS @shm @shn v ix ->
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    astIndexKnobsS (defaultKnobs {knobExpand = True})
                   (expandAst v)
                   (expandAstIxS ix)
  Ast.AstScatterS @shm @shn @shp v (var, ix) ->
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    astScatterS @shm @shn @shp (expandAst v) (var, expandAstIxS ix)
  Ast.AstAppendS x y -> astAppendS (expandAst x) (expandAst y)
  Ast.AstSliceS @i v -> astSliceS @i (expandAst v)
  Ast.AstReverseS v -> astReverseS (expandAst v)
  Ast.AstTransposeS perm v -> case v of
    Ast.AstVar{} -> t  -- normal form
    Ast.AstFromPrimal Ast.AstVar{} -> t  -- normal form
    Ast.AstPrimalPart Ast.AstVar{} -> t  -- normal form
    Ast.AstDualPart Ast.AstVar{} -> t  -- normal form
    Ast.AstProject1 Ast.AstVar{} -> t  -- normal form
    Ast.AstProject2 Ast.AstVar{} -> t  -- normal form
    Ast.AstProjectS Ast.AstVar{} _ -> t  -- normal form
    Ast.AstReplicate{} -> t  -- normal form
      -- TODO: this nf is silly, but right now transposes of replicates
      -- are small OR.Arrays and equivalent gathers are large OR.Arrays,
      -- so this has to stay. Maybe we should contract gathers back
      -- to transposes of replicates (not only to replicates). Or maybe
      -- we should extend orthotope to any gather schemes, not only
      -- the simple ones.
    AstSumOfList{} -> t  -- normal form
    AstN1S _ w | isVar w -> t  -- normal form
    AstN2S _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstR1S _ w | isVar w -> t  -- normal form
    Ast.AstR2S _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstScatterS @_ @_ @shp _ _
     | gcompare (Permutation.permRank perm)
                (shsRank $ knownShS @shp) == GGT -> t  -- nf
    _ ->  -- not nf, let's express all as a gather
      astTransposeAsGatherS (defaultKnobs {knobExpand = True})
                            perm  -- TODO: (normalizePermutation perm)
                            (expandAst v)
        -- this is expensive but the only way to guarantee full simplification
  Ast.AstReshapeS v -> case v of
    Ast.AstVar{} -> t  -- normal form
    Ast.AstFromPrimal Ast.AstVar{} -> t  -- normal form
    Ast.AstPrimalPart Ast.AstVar{} -> t  -- normal form
    Ast.AstDualPart Ast.AstVar{} -> t  -- normal form
    Ast.AstProject1 Ast.AstVar{} -> t  -- normal form
    Ast.AstProject2 Ast.AstVar{} -> t  -- normal form
    Ast.AstProjectS Ast.AstVar{} _ -> t  -- normal form
    AstSumOfList{} -> t  -- normal form
    AstN1S _ w | isVar w -> t  -- normal form
    AstN2S _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstR1S _ w | isVar w -> t  -- normal form
    Ast.AstR2S _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstScatterS{} -> t  -- normal form
    _ ->  -- not nf, let's express all as a gather
      astReshapeAsGatherS (defaultKnobs {knobExpand = True})
                          (expandAst v)
        -- this is expensive but the only way to guarantee full simplification
  Ast.AstGatherS @shm @shn @shp v (vars, ix) ->
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    astGatherKnobsS @shm @shn @shp
                    (defaultKnobs {knobExpand = True})
                    (expandAst v) (vars, expandAstIxS ix)
  Ast.AstZipS v -> Ast.AstZipS (expandAst v)
  Ast.AstUnzipS v -> Ast.AstUnzipS (expandAst v)

  Ast.AstRFromS v -> astRFromS $ expandAst v
  Ast.AstSFromR v -> astSFromR $ expandAst v
  Ast.AstSFromX v -> astSFromX $ expandAst v
  Ast.AstXFromS v -> astXFromS $ expandAst v

  Ast.AstXNestR @sh1 @m v ->
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    astXNestR $ expandAst v
  Ast.AstXNestS @sh1 @sh2 v ->
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    astXNestS $ expandAst v
  Ast.AstXNest @sh1 @sh2 v ->
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    astXNest $ expandAst v
  Ast.AstXUnNestR v -> astXUnNestR $ expandAst v
  Ast.AstXUnNestS v -> astXUnNestS $ expandAst v
  Ast.AstXUnNest v -> astXUnNest $ expandAst v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstReplicate0NR{} -> t
  Ast.AstSum0R{} -> t
  Ast.AstDot0R{} -> t
  Ast.AstDot1InR{} -> t
  Ast.AstMatvecmulR{} -> t
  Ast.AstMatmul2R{} -> t
  Ast.AstReplicate0NS{} -> t
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatvecmulS{} -> t
  Ast.AstMatmul2S{} -> t

  Ast.AstMkHVector l -> Ast.AstMkHVector $ V.map expandAstDynamic l
  Ast.AstProjectR l p -> astProjectR (expandAst l) p
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars (expandAst l) (expandAst v)
  Ast.AstProjectS l p -> astProjectS (expandAst l) p

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
      STKScalar{} ->
        contractRelOp opCodeRel (expandAst arg1) (expandAst arg2)
          -- Because the scalar tensors sometimes represent indexes,
          -- we expand them a bit more than all the others.
      _ -> Ast.AstRel opCodeRel (expandAst arg1) (expandAst arg2)


-- * The simplifying bottom-up pass

simplifyAstInt :: AstInt AstMethodLet -> AstInt AstMethodLet
simplifyAstInt = simplifyAst

simplifyAstIxR :: AstIxR AstMethodLet n -> AstIxR AstMethodLet n
simplifyAstIxR = fmap simplifyAstInt

simplifyAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
simplifyAstIxS = fmap simplifyAstInt

-- | This function guarantees full simplification: every redex
-- is visited and each combinator applied. The most exhaustive and costly
-- variants of each combinator are used, e.g., astIndexR.
simplifyAst
  :: forall s y. (AstSpan s, TensorKind y)
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
simplifyAst t = case t of
  Ast.AstPair t1 t2 -> astPair (simplifyAst t1) (simplifyAst t2)
  Ast.AstProject1 v -> astProject1 (simplifyAst v)
  Ast.AstProject2 v -> astProject2 (simplifyAst v)
  Ast.AstApply v ll -> astHApply (simplifyAstHFun v) (simplifyAst ll)
  Ast.AstVar{} -> t
  Ast.AstPrimalPart v -> astPrimalPart (simplifyAst v)
  Ast.AstDualPart v -> astDualPart (simplifyAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (simplifyAst v)
  Ast.AstD u u' -> Ast.AstD (simplifyAst u) (simplifyAst u')
  Ast.AstCond b a2 a3 ->
    astCond (simplifyAstBool b) (simplifyAst a2) (simplifyAst a3)
  Ast.AstFromVector snat l -> astFromVector snat (V.map simplifyAst l)
  Ast.AstSum snat stk v | Dict <- lemTensorKindOfBuild snat stk ->
    astSum snat stk (simplifyAst v)
  Ast.AstReplicate snat stk v | Dict <- lemTensorKindOfSTK stk ->
    astReplicate snat stk (simplifyAst v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, simplifyAst v)
  Ast.AstLet var u v -> astLet var (simplifyAst u) (simplifyAst v)
  AstConcrete{} -> t
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

  AstSumOfList stk args ->
    case isTensorInt t of
      Just Refl -> foldr1 contractAstPlusOp (map simplifyAst args)
      _ -> astSumOfList stk (map simplifyAst args)

  AstN1 opCode u ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp1 opCode (simplifyAst u)
      _ -> AstN1 opCode (simplifyAst u)
  AstN2 opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp2 opCode (simplifyAst u) (simplifyAst v)
      _ -> AstN2 opCode (simplifyAst u) (simplifyAst v)
  Ast.AstR1 opCode u -> Ast.AstR1 opCode (simplifyAst u)
  Ast.AstR2 opCode u v -> Ast.AstR2 opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2 opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstIntegralOp2 opCode (simplifyAst u) (simplifyAst v)
      _ -> Ast.AstI2 opCode (simplifyAst u) (simplifyAst v)
  Ast.AstFloor a -> Ast.AstFloor (simplifyAst a)
  Ast.AstFromIntegral v -> astFromIntegral $ simplifyAst v
  Ast.AstCast v -> astCast $ simplifyAst v

  AstN1R opCode u -> AstN1R opCode (simplifyAst u)
  AstN2R opCode u v -> AstN2R opCode (simplifyAst u) (simplifyAst v)
  Ast.AstR1R opCode u -> Ast.AstR1R opCode (simplifyAst u)
  Ast.AstR2R opCode u v -> Ast.AstR2R opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2R opCode u v -> Ast.AstI2R opCode (simplifyAst u) (simplifyAst v)
  Ast.AstFloorR a -> Ast.AstFloorR (simplifyAst a)
  Ast.AstFromIntegralR v -> astFromIntegralR $ simplifyAst v
  Ast.AstCastR v -> astCastR $ simplifyAst v
  Ast.AstMinIndexR a -> Ast.AstMinIndexR (simplifyAst a)
  Ast.AstMaxIndexR a -> Ast.AstMaxIndexR (simplifyAst a)
  Ast.AstIotaR{} -> t
  Ast.AstIndex v ix -> astIndexR (simplifyAst v) (simplifyAstIxR ix)
  Ast.AstScatter sh v (var, ix) ->
    astScatter sh (simplifyAst v) (var, simplifyAstIxR ix)
  Ast.AstAppend x y -> astAppend (simplifyAst x) (simplifyAst y)
  Ast.AstSlice i k v -> astSlice i k (simplifyAst v)
  Ast.AstReverse v -> astReverse (simplifyAst v)
  Ast.AstTranspose perm v ->
    astTranspose (normalizePermutation perm) (simplifyAst v)
  Ast.AstReshape sh v -> astReshape sh (simplifyAst v)
  Ast.AstGather sh v (vars, ix) ->
    astGatherR sh (simplifyAst v) (vars, simplifyAstIxR ix)
  Ast.AstZipR v -> Ast.AstZipR (simplifyAst v)
  Ast.AstUnzipR v -> Ast.AstUnzipR (simplifyAst v)

  Ast.AstFromScalar u -> astFromScalar $ simplifyAst u
  Ast.AstToScalar u -> Ast.AstToScalar $ simplifyAst u
  AstN1S opCode u -> AstN1S opCode (simplifyAst u)
  AstN2S opCode u v -> AstN2S opCode (simplifyAst u) (simplifyAst v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (simplifyAst u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (simplifyAst u) (simplifyAst v)
  Ast.AstFloorS a -> Ast.AstFloorS (simplifyAst a)
  Ast.AstFromIntegralS v -> astFromIntegralS $ simplifyAst v
  Ast.AstCastS v -> astCastS $ simplifyAst v
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (simplifyAst a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (simplifyAst a)
  Ast.AstIotaS -> t
  Ast.AstIndexS @shm @shn v ix ->
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    astIndexS (simplifyAst v) (simplifyAstIxS ix)
  Ast.AstScatterS @shm @shn @shp v (var, ix) ->
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    astScatterS @shm @shn @shp (simplifyAst v) (var, simplifyAstIxS ix)
  Ast.AstAppendS x y -> astAppendS (simplifyAst x) (simplifyAst y)
  Ast.AstSliceS @i v -> astSliceS @i (simplifyAst v)
  Ast.AstReverseS v -> astReverseS (simplifyAst v)
  Ast.AstTransposeS perm v -> astTransposeS perm $ simplifyAst v  -- TODO:(normalizePermutation perm)
  Ast.AstReshapeS v -> astReshapeS $ simplifyAst v
  Ast.AstGatherS @shm @shn @shp v (vars, ix) ->
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    astGatherS @shm @shn @shp (simplifyAst v) (vars, simplifyAstIxS ix)
  Ast.AstZipS v -> Ast.AstZipS (simplifyAst v)
  Ast.AstUnzipS v -> Ast.AstUnzipS (simplifyAst v)

  Ast.AstRFromS v -> astRFromS $ simplifyAst v
  Ast.AstSFromR v -> astSFromR $ simplifyAst v
  Ast.AstSFromX v -> astSFromX $ simplifyAst v
  Ast.AstXFromS v -> astXFromS $ simplifyAst v

  Ast.AstXNestR @sh1 @m v ->
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    astXNestR $ simplifyAst v
  Ast.AstXNestS @sh1 @sh2 v ->
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    astXNestS $ simplifyAst v
  Ast.AstXNest @sh1 @sh2 v ->
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    astXNest $ simplifyAst v
  Ast.AstXUnNestR v -> astXUnNestR $ simplifyAst v
  Ast.AstXUnNestS v -> astXUnNestS $ simplifyAst v
  Ast.AstXUnNest v -> astXUnNest $ simplifyAst v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstReplicate0NR{} -> t
  Ast.AstSum0R{} -> t
  Ast.AstDot0R{} -> t
  Ast.AstDot1InR{} -> t
  Ast.AstMatvecmulR{} -> t
  Ast.AstMatmul2R{} -> t
  Ast.AstReplicate0NS{} -> t
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatvecmulS{} -> t
  Ast.AstMatmul2S{} -> t

  Ast.AstMkHVector l -> Ast.AstMkHVector $ V.map simplifyAstDynamic l
  Ast.AstProjectR l p -> astProjectR (simplifyAst l) p
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars (simplifyAst l) (simplifyAst v)
  Ast.AstProjectS l p -> astProjectS (simplifyAst l) p

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
      STKScalar{} ->
        contractRelOp opCodeRel (simplifyAst arg1) (simplifyAst arg2)
          -- Because the scalar tensors sometimes represent indexes,
          -- we simplify them a bit more than all the others.
      _ -> Ast.AstRel opCodeRel (simplifyAst arg1) (simplifyAst arg2)


-- * The contraction (e.g., from gather expressions) bottom-up pass

-- When we have multiple backends, there should be one such pass
-- per backend that chooses a representation that is best for the backend.
-- Then AST should be extended with backend-specific constructors
-- and the interpreter would interpret all of them, but the simplifier
-- would ignore all and the user API would not make them available.
--
-- Note that unlike all the other code in this module, this function
-- is not written in a compositional style nor close to it,
-- but it's instead defined in an ad-hoc way based on benchmarks.
--
-- TODO: Move some of this to simplifyAst.
-- TODO: Generalize some of the extra term constructors and the rules.

contractAstInt :: AstInt AstMethodLet -> AstInt AstMethodLet
contractAstInt = contractAst

contractAstIxR :: AstIxR AstMethodLet n -> AstIxR AstMethodLet n
contractAstIxR = fmap contractAstInt

contractAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
contractAstIxS = fmap contractAstInt

contractAst
  :: forall s y. (AstSpan s, TensorKind y)
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
contractAst t = case t of
  Ast.AstPair t1 t2 -> astPair (contractAst t1) (contractAst t2)
  Ast.AstProject1 v -> astProject1 (contractAst v)
  Ast.AstProject2 v -> astProject2 (contractAst v)
  Ast.AstApply v ll -> astHApply (contractAstHFun v) (contractAst ll)
  Ast.AstVar{} -> t
  Ast.AstPrimalPart v -> astPrimalPart (contractAst v)
  Ast.AstDualPart v -> astDualPart (contractAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (contractAst v)
  Ast.AstD u u' -> Ast.AstD (contractAst u) (contractAst u')
  Ast.AstCond b a2 a3 ->
    astCond (contractAstBool b) (contractAst a2) (contractAst a3)
  Ast.AstFromVector snat l -> astFromVector snat (V.map contractAst l)
  Ast.AstSum snat stk (AstN2R TimesOp
                         (Ast.AstLet vart vt (Ast.AstTranspose tperm t2))
                         (Ast.AstTranspose uperm u))
   | Dict <- lemTensorKindOfSTK stk ->
      (Ast.AstLet
         vart
         (contractAst vt)
         (contractAst $ Ast.AstSum  -- the crucial exposed redex
            snat stk (AstN2R
                        TimesOp
                        (Ast.AstTranspose tperm (contractAst t2))
                        (Ast.AstTranspose uperm (contractAst u)))))
  Ast.AstSum snat stk (AstN2S TimesOp
                         (Ast.AstLet vart vt (Ast.AstTransposeS tperm t2))
                         (Ast.AstTransposeS uperm u))
   | Dict <- lemTensorKindOfSTK stk ->
      (Ast.AstLet
         vart
         (contractAst vt)
         (contractAst $ Ast.AstSum  -- the crucial exposed redex
            snat stk (AstN2S
                        TimesOp
                        (Ast.AstTransposeS tperm (contractAst t2))
                        (Ast.AstTransposeS uperm (contractAst u)))))
  Ast.AstSum snat stk (AstN2R TimesOp
                         (Ast.AstTranspose tperm t2)
                         (Ast.AstLet varu vu (Ast.AstTranspose uperm u)))
   | Dict <- lemTensorKindOfSTK stk ->
      (Ast.AstLet
         varu
         (contractAst vu)
         (contractAst $ Ast.AstSum  -- the crucial exposed redex
            snat stk (AstN2R
                        TimesOp
                        (Ast.AstTranspose tperm (contractAst t2))
                        (Ast.AstTranspose uperm (contractAst u)))))
  Ast.AstSum snat stk (AstN2S TimesOp
                         (Ast.AstTransposeS tperm t2)
                         (Ast.AstLet varu vu (Ast.AstTransposeS uperm u)))
   | Dict <- lemTensorKindOfSTK stk ->
      (Ast.AstLet
         varu
         (contractAst vu)
         (contractAst $ Ast.AstSum  -- the crucial exposed redex
            snat stk (AstN2S
                        TimesOp
                        (Ast.AstTransposeS tperm (contractAst t2))
                        (Ast.AstTransposeS uperm (contractAst u)))))
  Ast.AstSum snat stk (AstN2R TimesOp
                         (Ast.AstLet vart vt (Ast.AstTranspose tperm t2))
                         (Ast.AstLet varu vu (Ast.AstTranspose uperm u)))
   | Dict <- lemTensorKindOfSTK stk ->
      (Ast.AstLet
         vart
         (contractAst vt)
         (Ast.AstLet
            varu
            (contractAst vu)
            (contractAst $ Ast.AstSum  -- the crucial exposed redex
               snat stk (AstN2R
                           TimesOp
                           (Ast.AstTranspose tperm (contractAst t2))
                           (Ast.AstTranspose uperm (contractAst u))))))
  Ast.AstSum snat stk (AstN2S TimesOp
                         (Ast.AstLet vart vt (Ast.AstTransposeS tperm t2))
                         (Ast.AstLet varu vu (Ast.AstTransposeS uperm u)))
   | Dict <- lemTensorKindOfSTK stk ->
      (Ast.AstLet
         vart
         (contractAst vt)
         (Ast.AstLet
            varu
            (contractAst vu)
            (contractAst $ Ast.AstSum  -- the crucial exposed redex
               snat stk (AstN2S
                           TimesOp
                           (Ast.AstTransposeS tperm (contractAst t2))
                           (Ast.AstTransposeS uperm (contractAst u))))))
  Ast.AstSum snat stk@(STKR (SNat @n) (STKScalar rRep))
    v@(AstN2R TimesOp (Ast.AstTranspose tperm (Ast.AstReplicate _tk stkt t2))
                      (Ast.AstTranspose uperm (Ast.AstReplicate _uk stku u2)))
    | Just Refl <- sameNat (Proxy @n) (Proxy @2) -> case (stkt, stku) of
      (STKR{}, STKR{}) ->
        let interpretMatmul2 t3 u3 =
              let t4 = contractAst t3
                  u4 = contractAst u3
              in case testEquality rRep (typeRep @Double) of
                Just Refl -> Ast.AstMatmul2R t4 u4
                _ -> case testEquality rRep (typeRep @Float) of
                  Just Refl -> Ast.AstMatmul2R t4 u4
                  _ -> case testEquality rRep (typeRep @Int64) of
                    Just Refl -> Ast.AstMatmul2R t4 u4
                    _ -> case testEquality rRep (typeRep @CInt) of
                      Just Refl -> Ast.AstMatmul2R t4 u4
                      _ -> astSum snat stk (contractAst v)
        in case (tperm, uperm) of
          ([2, 1, 0], [1, 0]) ->  -- tk and uk are fine due to perms matching
            interpretMatmul2 t2 u2
          ([1, 0], [2, 1, 0]) ->
            interpretMatmul2 u2 t2
          ([2, 1, 0], [2, 0, 1]) ->
            interpretMatmul2 t2 (astTranspose [1, 0] u2)
          ([2, 0, 1], [2, 1, 0]) ->
            interpretMatmul2 u2 (astTranspose [1, 0] t2)
          ([1, 2, 0], [1, 0]) ->
            interpretMatmul2 (astTranspose [1, 0] t2) u2
          ([1, 0], [1, 2, 0]) ->
            interpretMatmul2 (astTranspose [1, 0] u2) t2
--          ([1, 2, 0], [2, 0, 1]) ->
--            interpretMatmul2 (astTranspose [1, 0] t2) (astTranspose [1, 0] u2)
--          ([2, 0, 1], [1, 2, 0]) ->
--            interpretMatmul2 (astTranspose [1, 0] u2) (astTranspose [1, 0] t2)
          -- The variants below emerge when the whole term is transposed.
          -- All overlap with variants above and the cheaper one is selected.
          ([2, 0, 1], [1, 2, 0]) ->
            Ast.AstTranspose [1, 0] $ interpretMatmul2 t2 u2
          ([1, 2, 0], [2, 0, 1]) ->
            Ast.AstTranspose [1, 0] $ interpretMatmul2 u2 t2
--          ([2, 0, 1], [2, 1, 0]) ->
--            Ast.AstTranspose [1, 0]
--            $ interpretMatmul2 t2 (astTranspose [1, 0] u2)
--          ([2, 1, 0], [2, 0, 1]) ->
--            Ast.AstTranspose [1, 0]
--            $ interpretMatmul2 u2 (astTranspose [1, 0] t2)
--          ([1, 2, 0], [1, 0]) ->
--            Ast.AstTranspose [1, 0]
--            $ interpretMatmul2 (astTranspose [1, 0] u2) t2
--          ([1, 0], [2, 1, 0]) ->
--            Ast.AstTranspose [1, 0]
--            $ interpretMatmul2 (astTranspose [1, 0] t2) (astTranspose [1, 0] u2)
--          ([2, 1, 0], [1, 0]) ->
--            Ast.AstTranspose [1, 0]
--            $ interpretMatmul2 (astTranspose [1, 0] u2) (astTranspose [1, 0] t2)
          _ -> astSum snat stk (contractAst v)
  Ast.AstSum
    snat@(SNat @m2)
    stk@(STKS (SNat @n2 :$$ SNat @p2 :$$ ZSS) (STKScalar @r rRep))
    v@(AstN2S TimesOp (Ast.AstTransposeS @permt permt
                         (Ast.AstReplicate (SNat @kt) (STKS @sht _ _) t2))
                      (Ast.AstTransposeS @permu permu
                         (Ast.AstReplicate (SNat @ku) (STKS @shu _ _) u2))) ->
    let perm10 = Permutation.makePerm @'[1, 0]
        attemptMatmul2
          :: forall m' n' p'. (KnownNat m', KnownNat n', KnownNat p')
          => AstTensor AstMethodLet s (TKS '[m', n'] r)
          -> AstTensor AstMethodLet s (TKS '[n', p'] r)
          -> Maybe (AstTensor AstMethodLet s (TKS '[m', p'] r))
        attemptMatmul2 t3 u3 =
          let t4 = contractAst t3
              u4 = contractAst u3
          in case testEquality rRep (typeRep @Double) of
            Just Refl ->
              Just $ Ast.AstMatmul2S
                       (SNat @m') (SNat @n') (SNat @p') t4 u4
            _ -> case testEquality rRep (typeRep @Float) of
              Just Refl ->
                Just $ Ast.AstMatmul2S
                         (SNat @m') (SNat @n') (SNat @p') t4 u4
              _ -> case testEquality rRep (typeRep @Int64) of
                Just Refl ->
                  Just $ Ast.AstMatmul2S
                           (SNat @m') (SNat @n') (SNat @p') t4 u4
                _ -> case testEquality rRep (typeRep @CInt) of
                  Just Refl ->
                    Just $ Ast.AstMatmul2S
                             (SNat @m') (SNat @n') (SNat @p') t4 u4
                  _ -> Nothing
    in fromMaybe (astSum snat stk (contractAst v))
       $ case (permt, permu) of
      ( SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permt (kt ': sht)
                      :~: [m2, n2, p2]) $
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permu (ku ': shu)
                      :~: [m2, n2, p2]) $
        -- Sadly, the casts below, though implied by the permutations
        -- (as edundantly spelled out by the casts above) are required
        -- to make it type-check and they easily mask bugs, too.
        -- In the result, this is as type-unsafe as ranked code would be.
        gcastWith (unsafeCoerceRefl :: sht :~: [n2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, p2]) $
        attemptMatmul2 t2 u2
      ( SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, p2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [n2, m2]) $
        attemptMatmul2 u2 t2
      ( SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [n2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [p2, m2]) $
        attemptMatmul2 t2 (astTransposeS perm10 u2)
      ( SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [p2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [n2, m2]) $
        attemptMatmul2 u2 (astTransposeS perm10 t2)
      ( SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, n2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, p2]) $
        attemptMatmul2 (astTransposeS perm10 t2) u2
      ( SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, p2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, n2]) $
        attemptMatmul2 (astTransposeS perm10 u2) t2
      ( SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, n2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [p2, m2]) $
        attemptMatmul2 (astTransposeS perm10 t2)
                       (astTransposeS perm10 u2)
      ( SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [p2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, n2]) $
        attemptMatmul2 (astTransposeS perm10 u2)
                       (astTransposeS perm10 t2)
      _ -> Nothing
  Ast.AstSum _ (STKR (SNat @n) _) (AstN2R TimesOp t2 u)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        Ast.AstDot0R (SNat @1) (contractAst t2) (contractAst u)
  Ast.AstSum k@SNat (STKS ZSS _) (AstN2S TimesOp t2 u) ->
    Ast.AstDot0S (k :$$ ZSS) (contractAst t2) (contractAst u)
  Ast.AstSum _ (STKR (SNat @n) _) (Ast.AstReshape @p _sh (AstN2R TimesOp t2 u))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        Ast.AstDot0R (SNat @p) (contractAst t2) (contractAst u)
  Ast.AstSum _ (STKS ZSS _) (Ast.AstReshapeS @sh2 (AstN2S TimesOp t2 u)) ->
    Ast.AstDot0S (knownShS @sh2) (contractAst t2) (contractAst u)
  Ast.AstSum _ (STKR (SNat @n) _) (Ast.AstTranspose [1, 0] (AstN2R TimesOp t2 u))
    -- TODO: generalize
    | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
        Ast.AstDot1InR (contractAst t2) (contractAst u)
  Ast.AstSum
    n@(SNat @n)
    (STKS (m@(SNat @m) :$$ ZSS) _)
    (Ast.AstTransposeS @perm @sh
       (SNat @n1 `Permutation.PCons` SNat @n0
        `Permutation.PCons` Permutation.PNil)
       (AstN2S TimesOp t2 u))
    -- TODO: generalize
-- TODO:    | Just Refl <- testEquality perm (Permutation.makePerm @'[1, 0]) ->
    | Just Refl <- sameNat (Proxy @n0) (Proxy @0)
    , Just Refl <- sameNat (Proxy @n1) (Proxy @1) ->
      -- TODO: Why is this needed? Would a more general lemma suffice?
      gcastWith (unsafeCoerceRefl
                 :: Permutation.PermutePrefix perm [n, m] :~: sh) $
      Ast.AstDot1InS m n (contractAst t2) (contractAst u)
  Ast.AstSum snat stk@(STKR (SNat @n) _) (Ast.AstReshape
                                            sh (Ast.AstTranspose _ t2))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        contractAst (Ast.AstSum snat stk (Ast.AstReshape sh t2))
  Ast.AstSum
    snat stk@(STKS ZSS _) (Ast.AstReshapeS
                             @sh3 @sh (Ast.AstTransposeS @_ @sh2 _ t2)) ->
    gcastWith (unsafeCoerceRefl :: Product sh2 :~: Product sh3) $
    contractAst (Ast.AstSum snat stk (Ast.AstReshapeS @sh2 @sh t2))
  Ast.AstSum snat stk@(STKR (SNat @n) _) (Ast.AstReshape
                                            sh (Ast.AstReverse t2))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        contractAst (Ast.AstSum snat stk (Ast.AstReshape sh t2))
  Ast.AstSum snat stk@(STKS ZSS _) (Ast.AstReshapeS
                                      @_ @sh (Ast.AstReverseS t2)) ->
    contractAst (Ast.AstSum snat stk (Ast.AstReshapeS @_ @sh t2))
  Ast.AstSum _ (STKR (SNat' @0) x)
             (Ast.AstReshape @n _sh (Ast.AstSum _ _ t2)) ->
    Ast.AstSum0R (SNat @(1 + n){- ~ 2 -}) x (contractAst t2)
  Ast.AstSum _k1 (STKS ZSS x)
             (Ast.AstReshapeS @sh (Ast.AstSum k2@SNat _ t2)) ->
    Ast.AstSum0S (k2 :$$ knownShS @sh {- ~ [k1] -}) x (contractAst t2)
  Ast.AstSum _ (STKR (SNat' @0) x) (Ast.AstSum _ _ t2)
    | Dict <- lemTensorKindOfSTK x ->
        Ast.AstSum0R (SNat @2) x (contractAst t2)
          -- TODO: more cases are needed
  Ast.AstSum k@SNat (STKS ZSS x) (Ast.AstSum k2@SNat _ t2)
    | Dict <- lemTensorKindOfSTK x ->
        Ast.AstSum0S (k2 :$$ k :$$ ZSS) x (contractAst t2)
          -- TODO: more cases are needed
  Ast.AstSum snat stk (Ast.AstLet var v t2) | Dict <- lemTensorKindOfSTK stk ->
    contractAst (Ast.AstLet var v (Ast.AstSum snat stk t2))
  Ast.AstSum snat stk (Ast.AstReshape sh (Ast.AstLet var v t2))
    | Dict <- lemTensorKindOfSTK stk ->
      contractAst (Ast.AstLet
                     var
                     v
                     (Ast.AstSum snat stk (Ast.AstReshape sh t2)))
  Ast.AstSum snat stk (Ast.AstReshapeS @sh (Ast.AstLet var v t2))
    | Dict <- lemTensorKindOfSTK stk ->
      contractAst (Ast.AstLet
                     var
                     v
                     (Ast.AstSum snat stk (Ast.AstReshapeS @sh t2)))
  Ast.AstSum _ (STKR (SNat' @0) x) (Ast.AstReshape @n _sh t2) ->
    Ast.AstSum0R (SNat @n) x (contractAst t2)
  Ast.AstSum _ (STKS ZSS x) (Ast.AstReshapeS @sh t2) ->
    Ast.AstSum0S (knownShS @sh) x (contractAst t2)
  Ast.AstSum snat stk v | Dict <- lemTensorKindOfBuild snat stk ->
    astSum snat stk (contractAst v)
  Ast.AstReplicate snat stk v | Dict <- lemTensorKindOfSTK stk ->
    astReplicate snat stk (contractAst v)
  -- These are only needed for tests that don't vectorize Ast.
  Ast.AstBuild1 @y2
                snat (var, Ast.AstSum
                             _ _ (AstN2R
                                    TimesOp t2 (Ast.AstIndex
                                                  u (AstIntVar var2 :.: ZIR))))
    | STKR (SNat @n) _ <- stensorKind @y2
    , Just Refl <- sameNat (Proxy @n) (Proxy @0)
    , var == var2, sNatValue snat == lengthAst u
    , not (varNameInAst var t2),  not (varNameInAst var u) ->
        Ast.AstMatvecmulR (contractAst u) (contractAst t2)
  Ast.AstBuild1 @y2
                snat (var, Ast.AstSum
                             n _
                             (AstN2S
                                TimesOp
                                t2
                                (Ast.AstIndexS
                                   u (((:.$) @m (AstIntVar var2) ZIS)))))
    | STKS ZSS _ <- stensorKind @y2
    , Just Refl <- geq snat (SNat @m)
    , var == var2
    , not (varNameInAst var t2),  not (varNameInAst var u) ->
        Ast.AstMatvecmulS snat n (contractAst u) (contractAst t2)
  Ast.AstBuild1 @y2
                snat (var, Ast.AstSum _ _
                             (Ast.AstReshape @p
                                _sh (AstN2R
                                       TimesOp t2 (Ast.AstIndex
                                                     u (AstIntVar var2
                                                        :.: ZIR)))))
    | STKR (SNat @n) _ <- stensorKind @y2
    , Just Refl <- sameNat (Proxy @n) (Proxy @0)
    , Just Refl <- sameNat (Proxy @p) (Proxy @1)
    , var == var2, sNatValue snat == lengthAst u
    , not (varNameInAst var t2),  not (varNameInAst var u) ->
        Ast.AstMatvecmulR (contractAst u) (contractAst t2)
  Ast.AstBuild1
    @y2 snat (var, Ast.AstSum _ _
                     (Ast.AstReshapeS
                        @sh (AstN2S
                               TimesOp
                               t2
                               (Ast.AstIndexS
                                  u (((:.$) @m (AstIntVar var2) ZIS))))))
    | STKS ZSS _ <- stensorKind @y2
    , n :$$ ZSS <- knownShS @sh
    , Just Refl <- geq snat (SNat @m)
    , var == var2
    , not (varNameInAst var t2),  not (varNameInAst var u) ->
        Ast.AstMatvecmulS snat n (contractAst u) (contractAst t2)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, contractAst v)
  Ast.AstLet var u v -> astLet var (contractAst u) (contractAst v)
  AstConcrete{} -> t
  Ast.AstMapAccumRDer @accShs @bShs @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfAD (stensorKind @accShs)
    , Dict <- lemTensorKindOfAD (stensorKind @bShs)
    , Dict <- lemTensorKindOfAD (stensorKind @eShs) ->
      Ast.AstMapAccumRDer k accShs bShs eShs
                          (contractAstHFun f)
                          (contractAstHFun df)
                          (contractAstHFun rf)
                          (contractAst acc0)
                          (contractAst es)
  Ast.AstMapAccumLDer @accShs @bShs @eShs k accShs bShs eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfAD (stensorKind @accShs)
    , Dict <- lemTensorKindOfAD (stensorKind @bShs)
    , Dict <- lemTensorKindOfAD (stensorKind @eShs) ->
      Ast.AstMapAccumLDer k accShs bShs eShs
                          (contractAstHFun f)
                          (contractAstHFun df)
                          (contractAstHFun rf)
                          (contractAst acc0)
                          (contractAst es)

  AstSumOfList stk args ->
    case isTensorInt t of
      Just Refl -> foldr1 contractAstPlusOp (map contractAst args)
      _ -> astSumOfList stk (map contractAst args)

  AstN1 opCode u ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp1 opCode (contractAst u)
      _ -> AstN1 opCode (contractAst u)
  AstN2 opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp2 opCode (contractAst u) (contractAst v)
      _ -> AstN2 opCode (contractAst u) (contractAst v)
  Ast.AstR1 opCode u -> Ast.AstR1 opCode (contractAst u)
  Ast.AstR2 opCode u v -> Ast.AstR2 opCode (contractAst u) (contractAst v)
  Ast.AstI2 opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstIntegralOp2 opCode (contractAst u) (contractAst v)
      _ -> Ast.AstI2 opCode (contractAst u) (contractAst v)
  Ast.AstFloor a -> Ast.AstFloor (contractAst a)
  Ast.AstFromIntegral v -> astFromIntegral $ contractAst v
  Ast.AstCast v -> astCast $ contractAst v

  AstN1R opCode u -> AstN1R opCode (contractAst u)
  AstN2R TimesOp v (Ast.AstLet var u
                      (Ast.AstReshape sh
                         (Ast.AstReplicate (SNat @m) stk s)))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v)
    , Dict <- lemTensorKindOfSTK stk ->
        -- The varNameInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        Ast.AstLet
          var
          (contractAst u)
          (AstN2R
             TimesOp v (Ast.AstReshape sh
                          (Ast.AstReplicate
                             (SNat @m) stk (contractAst s))))
  AstN2S TimesOp v (Ast.AstLet var u
                      (Ast.AstReshapeS @_ @sh
                         (Ast.AstReplicate (SNat @m) stk s)))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v)
    , Dict <- lemTensorKindOfSTK stk ->
        -- The varNameInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        Ast.AstLet
          var
          (contractAst u)
          (AstN2S
             TimesOp v (Ast.AstReshapeS @_ @sh
                          (Ast.AstReplicate
                             (SNat @m) stk (contractAst s))))
  AstN2R TimesOp v (Ast.AstReshape sh
                      (Ast.AstLet
                         var u (Ast.AstReplicate (SNat @m) stk s)))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v)
    , Dict <- lemTensorKindOfSTK stk ->
        Ast.AstLet
          var
          (contractAst u)
          (AstN2R
             TimesOp v (astReshape sh
                          (Ast.AstReplicate
                             (SNat @m) stk (contractAst s))))
  AstN2S TimesOp v (Ast.AstReshapeS @_ @sh
                      (Ast.AstLet
                         var u (Ast.AstReplicate (SNat @m) stk s)))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v)
    , Dict <- lemTensorKindOfSTK stk ->
        Ast.AstLet
          var
          (contractAst u)
          (AstN2S
             TimesOp v (astReshapeS @_ @sh
                          (Ast.AstReplicate
                             (SNat @m) stk (contractAst s))))
  AstN2R TimesOp v (Ast.AstLet var u (Ast.AstReplicate (SNat @m) stk s))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v)
    , Dict <- lemTensorKindOfSTK stk ->
        Ast.AstLet
          var
          (contractAst u)
          (AstN2R
              TimesOp v (Ast.AstReplicate
                           (SNat @m) stk (contractAst s)))
  AstN2S TimesOp v (Ast.AstLet var u (Ast.AstReplicate (SNat @m) stk s))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v)
    , Dict <- lemTensorKindOfSTK stk ->
        Ast.AstLet
          var
          (contractAst u)
          (AstN2S
              TimesOp v (Ast.AstReplicate
                           (SNat @m) stk (contractAst s)))
  AstN2R opCode u v -> AstN2R opCode (contractAst u) (contractAst v)
  Ast.AstR1R opCode u -> Ast.AstR1R opCode (contractAst u)
  Ast.AstR2R opCode u v -> Ast.AstR2R opCode (contractAst u) (contractAst v)
  Ast.AstI2R opCode u v -> Ast.AstI2R opCode (contractAst u) (contractAst v)
  Ast.AstFloorR a -> Ast.AstFloorR (contractAst a)
  Ast.AstFromIntegralR v -> astFromIntegralR $ contractAst v
  Ast.AstCastR v -> astCastR $ contractAst v
  Ast.AstMinIndexR a -> Ast.AstMinIndexR (contractAst a)
  Ast.AstMaxIndexR a -> Ast.AstMaxIndexR (contractAst a)
  Ast.AstIotaR{} -> t
  Ast.AstIndex Ast.AstIotaR{} (i :.: ZIR) ->
    astFromIntegralR $ astRFromS $ astFromScalar $ contractAstInt i
  Ast.AstIndex v ix -> astIndexR (contractAst v) (contractAstIxR ix)
  Ast.AstScatter sh v (var, ix) ->
    astScatter sh (contractAst v) (var, contractAstIxR ix)
  Ast.AstAppend x y -> astAppend (contractAst x) (contractAst y)
  Ast.AstSlice i k v -> astSlice i k (contractAst v)
  Ast.AstReverse v -> astReverse (contractAst v)
  Ast.AstTranspose perm v ->
    astTranspose (normalizePermutation perm) (contractAst v)
  Ast.AstReshape sh (Ast.AstReplicate _ (STKR @m _ x) s)
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
      Ast.AstReplicate0NR sh x (contractAst s)
  Ast.AstReshapeS @_ @sh (Ast.AstReplicate _ (STKS ZSS x) s) ->
      Ast.AstReplicate0NS (knownShS @sh) x (contractAst s)
  Ast.AstReshape sh (Ast.AstLet var v (Ast.AstReplicate snat stk t2))
    | Dict <- lemTensorKindOfSTK stk ->
      Ast.AstLet
        var
        (contractAst v)
        (astReshape sh (Ast.AstReplicate snat stk (contractAst t2)))
  Ast.AstReshapeS @_ @sh (Ast.AstLet var v (Ast.AstReplicate snat stk t2))
    | Dict <- lemTensorKindOfSTK stk ->
      Ast.AstLet
        var
        (contractAst v)
        (astReshapeS @_ @sh (Ast.AstReplicate snat stk (contractAst t2)))
  Ast.AstReshape sh v -> astReshape sh (contractAst v)
{- TODO, but sbuild is tricky, so only if benchmarks show it's worth it:
  AstGather sh AstIotaR (vars, i :.: ZIR) ->
    rbuild sh (interpretLambdaIndex
                 interpretAst env
                 (vars, fromPrimal @s $ AstFromIntegralR
                        $ AstRFromS $ AstFromScalar i)) -}
  Ast.AstGather sh v (vars, ix) ->
    astGatherR sh (contractAst v) (vars, contractAstIxR ix)
  Ast.AstZipR v -> Ast.AstZipR (contractAst v)
  Ast.AstUnzipR v -> Ast.AstUnzipR (contractAst v)

  Ast.AstFromScalar u -> astFromScalar $ contractAst u
  Ast.AstToScalar u -> Ast.AstToScalar $ contractAst u
  AstN1S opCode u -> AstN1S opCode (contractAst u)
  AstN2S opCode u v -> AstN2S opCode (contractAst u) (contractAst v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (contractAst u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (contractAst u) (contractAst v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (contractAst u) (contractAst v)
  Ast.AstFloorS a -> Ast.AstFloorS (contractAst a)
  Ast.AstFromIntegralS v -> astFromIntegralS $ contractAst v
  Ast.AstCastS v -> astCastS $ contractAst v
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (contractAst a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (contractAst a)
  Ast.AstIotaS -> t
  Ast.AstIndexS Ast.AstIotaS (i :.$ ZIS) ->
    astFromIntegralS $ astFromScalar $ contractAstInt i
  Ast.AstIndexS @shm @shn v ix ->
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    astIndexS (contractAst v) (contractAstIxS ix)
  Ast.AstScatterS @shm @shn @shp v (var, ix) ->
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    astScatterS @shm @shn @shp (contractAst v) (var, contractAstIxS ix)
  Ast.AstAppendS x y -> astAppendS (contractAst x) (contractAst y)
  Ast.AstSliceS @i v -> astSliceS @i (contractAst v)
  Ast.AstReverseS v -> astReverseS (contractAst v)
  Ast.AstTransposeS perm v -> astTransposeS perm $ contractAst v  -- TODO:(normalizePermutation perm)
  Ast.AstReshapeS v -> astReshapeS $ contractAst v
{- TODO, but sbuild is tricky, so only if benchmarks show it's worth it:
  AstGatherS @shm AstIotaS (vars, i :.$ ZIS) | Refl <- lemAppNil @shm ->
    gcastWith (unsafeCoerceRefl :: Drop (Rank shm) shm :~: '[]) $
    gcastWith (unsafeCoerceRefl :: Take (Rank shm) shm :~: shm) $
    sbuild @_ @_ @(Rank shm)
           (interpretLambdaIndexS
              interpretAst env
              (vars, fromPrimal @s $ AstFromIntegralS $ AstFromScalar i)) -}
  Ast.AstGatherS @shm @shn @shp v (vars, ix) ->
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    astGatherS @shm @shn @shp (contractAst v) (vars, contractAstIxS ix)
  Ast.AstZipS v -> Ast.AstZipS (contractAst v)
  Ast.AstUnzipS v -> Ast.AstUnzipS (contractAst v)

  Ast.AstRFromS v -> astRFromS $ contractAst v
  Ast.AstSFromR v -> astSFromR $ contractAst v
  Ast.AstSFromX v -> astSFromX $ contractAst v
  Ast.AstXFromS v -> astXFromS $ contractAst v

  Ast.AstXNestR @sh1 @m v ->
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    astXNestR $ contractAst v
  Ast.AstXNestS @sh1 @sh2 v ->
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    astXNestS $ contractAst v
  Ast.AstXNest @sh1 @sh2 v ->
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    astXNest $ contractAst v
  Ast.AstXUnNestR v -> astXUnNestR $ contractAst v
  Ast.AstXUnNestS v -> astXUnNestS $ contractAst v
  Ast.AstXUnNest v -> astXUnNest $ contractAst v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstReplicate0NR{} -> t
  Ast.AstSum0R{} -> t
  Ast.AstDot0R{} -> t
  Ast.AstDot1InR{} -> t
  Ast.AstMatvecmulR{} -> t
  Ast.AstMatmul2R{} -> t
  Ast.AstReplicate0NS{} -> t
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatvecmulS{} -> t
  Ast.AstMatmul2S{} -> t

  Ast.AstMkHVector l -> Ast.AstMkHVector $ V.map contractAstDynamic l
  Ast.AstProjectR l p -> astProjectR (contractAst l) p
  Ast.AstLetHVectorIn vars l v ->
    astLetHVectorIn vars (contractAst l) (contractAst v)
  Ast.AstProjectS l p -> astProjectS (contractAst l) p

contractAstDynamic
  :: AstSpan s
  => AstDynamic AstMethodLet s -> AstDynamic AstMethodLet s
contractAstDynamic (DynamicRanked u) =
  DynamicRanked $ contractAst u
contractAstDynamic (DynamicShaped u) =
  DynamicShaped $ contractAst u
contractAstDynamic u@DynamicRankedDummy{} = u
contractAstDynamic u@DynamicShapedDummy{} = u

contractAstHFun :: TensorKind y => AstHFun x y -> AstHFun x y
contractAstHFun = \case
  Ast.AstLambda ~(vvars, ftk, l) ->
    Ast.AstLambda (vvars, ftk, contractAst l)

contractAstBool :: AstBool AstMethodLet -> AstBool AstMethodLet
contractAstBool t = case t of
  Ast.AstBoolNot (AstBoolConst b) -> AstBoolConst $ not b
  Ast.AstBoolNot arg -> Ast.AstBoolNot $ contractAstBool arg
  Ast.AstB2 opCodeBool arg1 arg2 ->
    contractAstB2 opCodeBool (contractAstBool arg1) (contractAstBool arg2)
  AstBoolConst{} -> t
  Ast.AstRel @y3 opCodeRel arg1 arg2 ->
    case stensorKind @y3 of
      STKScalar{} ->
        contractRelOp opCodeRel (contractAst arg1) (contractAst arg2)
      _ -> Ast.AstRel opCodeRel (contractAst arg1) (contractAst arg2)


-- * Contraction of arithmetic and boolean operation terms

contractRelOp :: GoodScalar r
              => OpCodeRel
              -> AstTensor AstMethodLet PrimalSpan (TKScalar r)
              -> AstTensor AstMethodLet PrimalSpan (TKScalar r)
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
contractAstPlusOp (AstSumOfList _ (AstConcrete _ u : lu))
                  (AstSumOfList _ (AstConcrete _ v : lv)) =
  addConstToList (u + v) (lu ++ lv)
contractAstPlusOp (AstSumOfList stk lu)
                  (AstSumOfList _ (AstConcrete ftk v : lv)) =
  AstSumOfList stk (AstConcrete ftk v : lv ++ lu)
contractAstPlusOp (AstSumOfList stk lu)
                  (AstSumOfList _ lv) =
  AstSumOfList stk (lu ++ lv)

contractAstPlusOp (AstConcrete _ u)
                  (AstSumOfList _ (AstConcrete _ v : lv)) =
  addConstToList (u + v) lv
contractAstPlusOp u
                  (AstSumOfList stk (AstConcrete ftk v : lv)) =
  AstSumOfList stk (AstConcrete ftk v : u : lv)
contractAstPlusOp u
                  (AstSumOfList stk lv) =
  AstSumOfList stk (u : lv)

contractAstPlusOp (AstSumOfList _ (AstConcrete _ u : lu))
                  (AstConcrete _ v) =
  addConstToList (u + v) lu
contractAstPlusOp (AstSumOfList stk (AstConcrete ftk u : lu))
                  v =
  AstSumOfList stk (AstConcrete ftk u : v : lu)
contractAstPlusOp (AstSumOfList stk lu)
                  v =
  AstSumOfList stk (v : lu)

contractAstPlusOp (AstConcrete ftk u) (AstConcrete _ v) = AstConcrete ftk $ u + v
contractAstPlusOp u (AstConcrete _ v) = addConstToList v [u]
contractAstPlusOp (AstConcrete _ u) v = addConstToList u [v]

-- Unfortunately, these won't fire if the required terms are scattered
-- among elements of the AstSumOfList list. However, in many cases,
-- binary addition is used interspersed with other operations,
-- so longer lists don't form and so these terms have a chance to be adjacent,
-- especially that AstConcrete is guaranteed not to intervene.
contractAstPlusOp (AstN1 NegateOp (Ast.AstVar _ var))
                  (Ast.AstVar _ var')
  | var == var' = 0
contractAstPlusOp (Ast.AstVar _ var')
                  (AstN1 NegateOp (Ast.AstVar _ var))
  | var == var' = 0
contractAstPlusOp
  (Ast.AstI2 RemOp (AstN1 NegateOp (Ast.AstVar _ var)) (AstConcrete _ v))
  (Ast.AstI2 RemOp (Ast.AstVar _ var') (AstConcrete _ v'))
  | var == var' && v == v' = 0
contractAstPlusOp
  (Ast.AstI2 RemOp (Ast.AstVar _ var') (AstConcrete _ v'))
  (Ast.AstI2 RemOp (AstN1 NegateOp (Ast.AstVar _ var)) (AstConcrete _ v))
  | var == var' && v == v' = 0

contractAstPlusOp u v = AstSumOfList stensorKind [u, v]

addConstToList :: RepN (TKScalar Int64) -> [AstInt AstMethodLet]
               -> AstInt AstMethodLet
addConstToList _ [] = error "addConstToList: AstSumOfList list too short"
addConstToList a [i] =
  if unRepN a == 0
  then i
  else AstSumOfList stensorKind [AstConcrete FTKScalar a, i]
addConstToList a l =
  if unRepN a == 0
  then AstSumOfList stensorKind l
  else AstSumOfList stensorKind (AstConcrete FTKScalar a : l)

contractAstNumOp1 :: OpCodeNum1 -> AstInt AstMethodLet -> AstInt AstMethodLet
contractAstNumOp1 NegateOp (AstConcrete ftk u) = AstConcrete ftk $ negate u
contractAstNumOp1 NegateOp (AstSumOfList _ l) =
  foldr1 contractAstPlusOp (map (contractAstNumOp1 NegateOp) l)
contractAstNumOp1 NegateOp (AstN2 TimesOp (AstConcrete ftk u) v) =
  contractAstNumOp2 TimesOp (AstConcrete ftk $ negate u) v
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

contractAstNumOp1 AbsOp (AstConcrete ftk u) = AstConcrete ftk $ abs u
contractAstNumOp1 AbsOp (AstN1 AbsOp u) = AstN1 AbsOp u
contractAstNumOp1 AbsOp (AstN1 NegateOp u) = contractAstNumOp1 AbsOp u
contractAstNumOp1 SignumOp (AstConcrete ftk u) = AstConcrete ftk $ signum u
contractAstNumOp1 SignumOp (AstN1 SignumOp u) = AstN1 SignumOp u
contractAstNumOp1 SignumOp (AstN1 AbsOp u) =
  contractAstNumOp1 AbsOp (AstN1 SignumOp u)

contractAstNumOp1 opCode u = AstN1 opCode u

contractAstNumOp2 :: OpCodeNum2 -> AstInt AstMethodLet -> AstInt AstMethodLet -> AstInt AstMethodLet
contractAstNumOp2 MinusOp u v =
  contractAstPlusOp u (contractAstNumOp1 NegateOp v)
contractAstNumOp2 TimesOp (AstConcrete ftk u) (AstConcrete _ v) = AstConcrete ftk $ u * v
contractAstNumOp2 TimesOp (AstConcrete ftk i) _v | unRepN i == 0 = AstConcrete ftk i
contractAstNumOp2 TimesOp _u (AstConcrete ftk i) | unRepN i == 0 = AstConcrete ftk i
contractAstNumOp2 TimesOp (AstConcrete _ i) v | unRepN i == 1 = v
contractAstNumOp2 TimesOp u (AstConcrete _ i) | unRepN i == 1 = u
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
contractAstNumOp2 TimesOp (AstSumOfList _ l) w@AstConcrete{} =
  foldr1 contractAstPlusOp (map (\u -> contractAstNumOp2 TimesOp u w) l)
contractAstNumOp2 TimesOp u@AstConcrete{} (AstSumOfList _ l) =
  foldr1 contractAstPlusOp (map (contractAstNumOp2 TimesOp u) l)
-- TODO: perhaps aim for a polynomial normal form? but that requires global
-- inspection of the whole expression
contractAstNumOp2 TimesOp (AstConcrete ftk u) (AstN2 TimesOp (AstConcrete _ v) w) =
  contractAstNumOp2 TimesOp (AstConcrete ftk $ u * v) w
contractAstNumOp2 TimesOp u (AstConcrete ftk n) =
  contractAstNumOp2 TimesOp (AstConcrete ftk n) u
contractAstNumOp2 TimesOp (AstN2 TimesOp u v) w =
  contractAstNumOp2 TimesOp u (contractAstNumOp2 TimesOp v w)

-- With static shapes, the second argument to QuotOp and RemOp
-- is often a constant, which makes such rules worth including,
-- since they are likely to fire. To help them fire, we avoid changing
-- that constant, if possible, e.g., in rules for NegateOp.
contractAstNumOp2
  TimesOp (AstConcrete ftk v)
          (Ast.AstI2 QuotOp (Ast.AstVar sh var) (AstConcrete _ v')) | v == v' =
    contractAstNumOp2 MinusOp
                      (Ast.AstVar sh var)
                      (Ast.AstI2 RemOp (Ast.AstVar sh var) (AstConcrete ftk v))
contractAstNumOp2 opCode u v = AstN2 opCode u v

contractAstIntegralOp2 :: OpCodeIntegral2 -> AstInt AstMethodLet -> AstInt AstMethodLet -> AstInt AstMethodLet
contractAstIntegralOp2 QuotOp (AstConcrete ftk u) (AstConcrete _ v) = AstConcrete ftk $ quotF u v
contractAstIntegralOp2 QuotOp (AstConcrete ftk i) _v | unRepN i == 0 = AstConcrete ftk i
contractAstIntegralOp2 QuotOp u (AstConcrete _ i) | unRepN i == 1 = u
contractAstIntegralOp2 QuotOp (Ast.AstI2 RemOp _u (AstConcrete _ v)) (AstConcrete _ v')
  | v' >= v && v >= 0 = 0
contractAstIntegralOp2 QuotOp (Ast.AstI2 QuotOp u v) w =
  contractAstIntegralOp2 QuotOp u (contractAstNumOp2 TimesOp v w)
contractAstIntegralOp2 QuotOp (Ast.AstN2 TimesOp (AstConcrete _ u) v) (AstConcrete _ u')
  | u == u' = v

contractAstIntegralOp2 RemOp (AstConcrete ftk u) (AstConcrete _ v) = AstConcrete ftk $ remF u v
contractAstIntegralOp2 RemOp (AstConcrete ftk i) _v | unRepN i == 0 = AstConcrete ftk i
contractAstIntegralOp2 RemOp _u (AstConcrete ftk i) | unRepN i == 1 = AstConcrete ftk $ RepN 0
contractAstIntegralOp2 RemOp (Ast.AstI2 RemOp u (AstConcrete ftk v)) (AstConcrete _ v')
  | v' >= v && v >= 0 = Ast.AstI2 RemOp u (AstConcrete ftk v)
contractAstIntegralOp2 RemOp (Ast.AstI2 RemOp u (AstConcrete ftk v)) (AstConcrete _ v')
  | remF v v' == 0 && v > 0 = contractAstIntegralOp2 RemOp u (AstConcrete ftk v')
contractAstIntegralOp2 RemOp (AstN2 TimesOp (AstConcrete _ u) _v) (AstConcrete _ u')
  | remF u u' == 0 = 0

contractAstIntegralOp2 opCode u v = Ast.AstI2 opCode u v

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

substituteAstIxR
  :: (AstSpan s2, GoodScalar r2)
  => AstTensor AstMethodLet s2 (TKScalar r2) -> AstVarName s2 (TKScalar r2)
  -> AstIxR AstMethodLet n
  -> AstIxR AstMethodLet n
substituteAstIxR i var ix =
  fromMaybe ix $ substitute1AstIxR i var ix

substituteAstIxS
  :: (AstSpan s2, GoodScalar r2)
  => AstTensor AstMethodLet s2 (TKScalar r2) -> AstVarName s2 (TKScalar r2)
  -> AstIxS AstMethodLet sh
  -> AstIxS AstMethodLet sh
substituteAstIxS i var ix =
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
  Ast.AstPair u v ->
    case (substitute1Ast i var u, substitute1Ast i var v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) -> Just $ astPair (fromMaybe u mu) (fromMaybe v mv)
  Ast.AstProject1 a -> astProject1 <$> substitute1Ast i var a
  Ast.AstProject2 a -> astProject2 <$> substitute1Ast i var a
  Ast.AstApply t ll ->
    case ( substitute1AstHFun i var t
         , substitute1Ast i var ll ) of
      (Nothing, Nothing) -> Nothing
      (mt, mll) -> Just $ astHApply (fromMaybe t mt) (fromMaybe ll mll)
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
  Ast.AstFromVector snat args ->
    let margs = V.map (substitute1Ast i var) args
    in if V.any isJust margs
       then Just $ astFromVector snat $ V.zipWith fromMaybe args margs
       else Nothing
  Ast.AstSum snat stk v | Dict <- lemTensorKindOfBuild snat stk ->
    astSum snat stk <$> substitute1Ast i var v
  Ast.AstReplicate snat stk v | Dict <- lemTensorKindOfSTK stk ->
    astReplicate snat stk <$> substitute1Ast i var v
  Ast.AstBuild1 k (var2, v) ->
    assert (varNameToAstVarId var2 /= varNameToAstVarId var) $
    Ast.AstBuild1 k . (var2,) <$> substitute1Ast i var v
  Ast.AstLet var2 u v ->
    case (substitute1Ast i var u, substitute1Ast i var v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) -> Just $ astLet var2 (fromMaybe u mu) (fromMaybe v mv)
  Ast.AstConcrete{} -> Nothing
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

  Ast.AstSumOfList stk args ->
    let margs = map (substitute1Ast i var) args
    in if any isJust margs
       then Just $ case isTensorInt v1 of
         Just Refl -> foldr1 contractAstPlusOp $ zipWith fromMaybe args margs
         _ -> astSumOfList stk $ zipWith fromMaybe args margs
       else Nothing

  Ast.AstN1 opCode u ->
    (\u2 -> case isTensorInt u2 of
       Just Refl -> contractAstNumOp1 opCode u2
       _ -> Ast.AstN1 opCode u2)
    <$> substitute1Ast i var u
  Ast.AstN2 opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ case isTensorInt u of
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
       then Just $ case isTensorInt u of
         Just Refl ->
           contractAstIntegralOp2 opCode (fromMaybe u mu) (fromMaybe v mv)
         _ -> Ast.AstI2 opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstFloor a -> Ast.AstFloor <$> substitute1Ast i var a
  Ast.AstFromIntegral v -> astFromIntegral <$> substitute1Ast i var v
  Ast.AstCast v -> astCast <$> substitute1Ast i var v

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
  Ast.AstFloorR a -> Ast.AstFloorR <$> substitute1Ast i var a
  Ast.AstFromIntegralR v -> astFromIntegralR <$> substitute1Ast i var v
  Ast.AstCastR v -> astCastR <$> substitute1Ast i var v
  Ast.AstMinIndexR a -> Ast.AstMinIndexR <$> substitute1Ast i var a
  Ast.AstMaxIndexR a -> Ast.AstMaxIndexR <$> substitute1Ast i var a
  Ast.AstIotaR{} -> Nothing
  Ast.AstIndex v ix ->
    case (substitute1Ast i var v, substitute1AstIxR i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astIndexR (fromMaybe v mv) (fromMaybe ix mix)
  Ast.AstScatter sh v (vars, ix) ->
    case (substitute1Ast i var v, substitute1AstIxR i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astScatter sh (fromMaybe v mv)
                                        (vars, fromMaybe ix mix)
  Ast.AstAppend x y ->
    case (substitute1Ast i var x, substitute1Ast i var y) of
      (Nothing, Nothing) -> Nothing
      (mx, my) -> Just $ astAppend (fromMaybe x mx) (fromMaybe y my)
  Ast.AstSlice i2 n v -> astSlice i2 n <$> substitute1Ast i var v
  Ast.AstReverse v -> astReverse <$> substitute1Ast i var v
  Ast.AstTranspose perm v -> astTranspose perm <$> substitute1Ast i var v
  Ast.AstReshape sh v -> astReshape sh <$> substitute1Ast i var v
  Ast.AstGather sh v (vars, ix) ->
    case (substitute1Ast i var v, substitute1AstIxR i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astGatherR sh (fromMaybe v mv)
                                        (vars, fromMaybe ix mix)
  Ast.AstZipR v -> Ast.AstZipR <$> substitute1Ast i var v
  Ast.AstUnzipR v -> Ast.AstUnzipR <$> substitute1Ast i var v

  Ast.AstFromScalar u -> astFromScalar <$> substitute1Ast i var u
  Ast.AstToScalar u -> Ast.AstToScalar <$> substitute1Ast i var u
  Ast.AstN1S opCode u -> Ast.AstN1S opCode  <$> substitute1Ast i var u
  Ast.AstN2S opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstN2S opCode (fromMaybe u mu) (fromMaybe v mv)
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
       then Just $ Ast.AstI2S opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstFloorS a -> Ast.AstFloorS <$> substitute1Ast i var a
  Ast.AstFromIntegralS a -> astFromIntegralS <$> substitute1Ast i var a
  Ast.AstCastS v -> astCastS <$> substitute1Ast i var v
  Ast.AstMinIndexS a -> Ast.AstMinIndexS <$> substitute1Ast i var a
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS <$> substitute1Ast i var a
  Ast.AstIotaS -> Nothing
  Ast.AstIndexS @shm @shn v ix ->
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    case (substitute1Ast i var v, substitute1AstIxS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astIndexS (fromMaybe v mv) (fromMaybe ix mix)
  Ast.AstScatterS @shm @shn @shp v (vars, ix) ->
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    case (substitute1Ast i var v, substitute1AstIxS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astScatterS @shm @shn @shp
                                      (fromMaybe v mv)
                                      (vars, fromMaybe ix mix)
  Ast.AstAppendS x y ->
    case (substitute1Ast i var x, substitute1Ast i var y) of
      (Nothing, Nothing) -> Nothing
      (mx, my) -> Just $ astAppendS (fromMaybe x mx) (fromMaybe y my)
  Ast.AstSliceS @i v -> astSliceS @i <$> substitute1Ast i var v
  Ast.AstReverseS v -> astReverseS <$> substitute1Ast i var v
  Ast.AstTransposeS perm v -> astTransposeS perm <$> substitute1Ast i var v
  Ast.AstReshapeS v -> astReshapeS <$> substitute1Ast i var v
  Ast.AstGatherS @shm @shn @shp v (vars, ix) ->
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    case (substitute1Ast i var v, substitute1AstIxS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astGatherS @shm @shn @shp
                                     (fromMaybe v mv)
                                     (vars, fromMaybe ix mix)
  Ast.AstZipS v -> Ast.AstZipS <$> substitute1Ast i var v
  Ast.AstUnzipS v -> Ast.AstUnzipS <$> substitute1Ast i var v

  Ast.AstRFromS v -> astRFromS <$> substitute1Ast i var v
  Ast.AstSFromR v -> astSFromR <$> substitute1Ast i var v
  Ast.AstSFromX v -> astSFromX <$> substitute1Ast i var v
  Ast.AstXFromS v -> astXFromS <$> substitute1Ast i var v

  Ast.AstXNestR @sh1 @m v ->
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    astXNestR <$> substitute1Ast i var v
  Ast.AstXNestS @sh1 @sh2 v ->
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    astXNestS <$> substitute1Ast i var v
  Ast.AstXNest @sh1 @sh2 v ->
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    astXNest <$> substitute1Ast i var v
  Ast.AstXUnNestR v -> astXUnNestR <$> substitute1Ast i var v
  Ast.AstXUnNestS v -> astXUnNestS <$> substitute1Ast i var v
  Ast.AstXUnNest v -> astXUnNest <$> substitute1Ast i var v

  Ast.AstReplicate0NR sh stk v | Dict <- lemTensorKindOfSTK stk ->
    Ast.AstReplicate0NR sh stk <$> substitute1Ast i var v
  Ast.AstSum0R snat@SNat stk v | Dict <- lemTensorKindOfSTK stk ->
    Ast.AstSum0R snat stk <$> substitute1Ast i var v
  Ast.AstDot0R snat@SNat u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstDot0R snat (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstDot1InR u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstDot1InR (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstMatvecmulR u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstMatvecmulR (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstMatmul2R u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstMatmul2R (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstReplicate0NS sh stk v | Dict <- lemTensorKindOfSTK stk ->
    Ast.AstReplicate0NS sh stk <$> substitute1Ast i var v
  Ast.AstSum0S sh stk v | Dict <- lemTensorKindOfSTK stk ->
    withKnownShS sh $
    Ast.AstSum0S sh stk <$> substitute1Ast i var v
  Ast.AstDot0S sh u v ->
    withKnownShS sh $
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstDot0S sh (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstDot1InS m@SNat n@SNat u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstDot1InS  m n(fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstMatvecmulS m@SNat n@SNat u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstMatvecmulS m n (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstMatmul2S m@SNat n@SNat p@SNat u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstMatmul2S m n p (fromMaybe u mu) (fromMaybe v mv)
       else Nothing

  Ast.AstMkHVector args ->
    let margs = V.map (substitute1AstDynamic i var) args
    in if V.any isJust margs
       then Just $ Ast.AstMkHVector $ V.zipWith fromMaybe args margs
       else Nothing
  Ast.AstProjectR l p ->
    case substitute1Ast i var l of
      Nothing -> Nothing
      ml -> Just $ astProjectR (fromMaybe l ml) p
  Ast.AstLetHVectorIn vars l v ->
    case (substitute1Ast i var l, substitute1Ast i var v) of
      (Nothing, Nothing) -> Nothing
      (ml, mv) ->
        Just $ astLetHVectorIn vars (fromMaybe l ml) (fromMaybe v mv)
  Ast.AstProjectS l p ->
    case substitute1Ast i var l of
      Nothing -> Nothing
      ml -> Just $ astProjectS (fromMaybe l ml) p

substitute1AstIxR
  :: (AstSpan s2, TensorKind y)
  => AstTensor AstMethodLet s2 y -> AstVarName s2 y -> AstIxR AstMethodLet n
  -> Maybe (AstIxR AstMethodLet n)
substitute1AstIxR i var ix =
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
     then Just $ zipWith_IndexS fromMaybe ix mix
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
                   => AstTensor AstMethodLet s2 y -> AstVarName s2 y
                   -> AstBool AstMethodLet
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
         STKScalar{} ->
           Just $ contractRelOp opCodeRel (fromMaybe arg1 mr1)
                                          (fromMaybe arg2 mr2)
         _ -> Just $ Ast.AstRel opCodeRel (fromMaybe arg1 mr1)
                                          (fromMaybe arg2 mr2)
       else Nothing
