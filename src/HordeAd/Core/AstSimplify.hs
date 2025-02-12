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
  ( -- * The simplifying combinators, one for almost each AST constructor
    astPair, astProject1, astProject2, astFromVector, astSum, astReplicate
  , astMapAccumRDer, astMapAccumLDer, astApply, astCond, astConcrete

  , astLet

  , astPrimalPart, astDualPart

  , astSumOfList

  , astFromIntegralK, astCastK

  , astFromIntegralS, astCastS

  , astIndexStepS, astScatterS, astGatherStepS
  , astAppendS, astSliceS, astReverseS, astTransposeS, astReshapeS
  , astNestS, astUnNestS

  , astFromS, astSFromK, astSFromR, astSFromX

    -- * Helper combinators
  , astLetFun
    -- * A cheap simplification of only the topmost nodes
  , astNonIndexStep
    -- * The expansion (e.g., into gather expressions) bottom-up pass
  , expandAst
    -- * The simplifying bottom-up pass
  , simplifyAst
    -- * The contraction (e.g., from gather expressions) bottom-up pass
  , contractAst
    -- * Substitution operation
  , substituteAst, substituteAstIxS
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Control.Monad (mapAndUnzipM, mplus)
import Data.Default
import Data.Foldable qualified as Foldable
import Data.Functor.Const
import Data.GADT.Compare
import Data.Int (Int64)
import Data.List (dropWhileEnd)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (catMaybes, fromMaybe, isJust)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Type.Ord (Compare)
import Data.Vector.Generic qualified as V
import Data.Vector.Strict qualified as Data.Vector
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
  )
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (typeRep)

import Data.Array.Mixed.Lemmas
import Data.Array.Mixed.Permutation (DropLen, Perm (..), TakeLen, permInverse)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (ssxFromShape, withKnownShX)
import Data.Array.Mixed.Types (Init, Last, Tail, unsafeCoerceRefl)
import Data.Array.Nested
  (IxS (..), ListS (..), Product, Rank, ShS (..), type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Lemmas
import Data.Array.Nested.Internal.Shape
  ( ixsAppend
  , ixsInit
  , ixsLast
  , ixsPermutePrefix
  , listsAppend
  , listsFmap
  , listsInit
  , listsLast
  , listsRank
  , listsToList
  , shCvtSX
  , shrRank
  , shsAppend
  , shsLast
  , shsLength
  , shsPermute
  , shsPermutePrefix
  , shsRank
  , shsTakeLen
  , withKnownShS
  )
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.Ast
  ( AstBool (AstBoolConst)
  , AstTensor (AstConcrete, AstN1K, AstN1S, AstN2K, AstN2S, AstSumOfList)
  )
import HordeAd.Core.Ast hiding (AstBool (..), AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersAst ()
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Ops
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

-- * Expressing operations as Gather; introduces new variable names

data SimplifyKnobs = SimplifyKnobs
  { knobStepOnly :: Bool
  , knobExpand   :: Bool
  }

defaultKnobs :: SimplifyKnobs
defaultKnobs = SimplifyKnobs False False

-- We keep AstTranspose terms for as long as possible, because
-- they are small and fuse nicely in many cases. For some forms of indexing
-- and nesting with reshape and gather they don't fuse, which is when
-- this function is invoked.
astTransposeAsGatherS
  :: forall perm sh s r. AstSpan s
  => SimplifyKnobs -> Permutation.Perm perm
  -> AstTensor AstMethodLet s (TKS2 sh r)
  -> AstTensor AstMethodLet s (TKS2 (Permutation.PermutePrefix perm sh) r)
{-# NOINLINE astTransposeAsGatherS #-}
astTransposeAsGatherS knobs perm v =
  let STKS shn _ = ftkToSTK (ftkAst v)
      shnPermuted = shsPermute perm (shsTakeLen perm shn)
  in funToVarsIxS @_ @AstMethodLet shnPermuted $ \ (!vars, !ix) ->
    -- See astGatherCase.AstTransposeS for an example with more comments.
    gcastWith (lemRankMapJust $ shsTakeLen perm shn) $
    gcastWith (unsafeCoerceRefl :: Rank (TakeLen perm sh) :~: Rank perm) $
    permInverse perm $ \(invperm :: Nested.Perm invperm) proof ->
      case proof (ssxFromShape $ shCvtSX $ shsTakeLen perm shn) of
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
                             knobs (shsDropLen perm shn) v (vars, asts)

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
astReshapeAsGatherS
  :: forall sh sh2 r s. AstSpan s
  => SimplifyKnobs -> ShS sh2 -> AstTensor AstMethodLet s (TKS2 sh r)
  -> AstTensor AstMethodLet s (TKS2 sh2 r)
{-# NOINLINE astReshapeAsGatherS #-}
astReshapeAsGatherS knobs shOut v | Refl <- lemAppNil @sh2
                                  , Refl <- lemAppNil @sh
                                  , STKS shIn _ <- ftkToSTK (ftkAst v) =
  funToVarsIxS shOut $ \ (!vars, !ix) ->
    let fromInt :: Int -> AstInt AstMethodLet
        fromInt i = AstConcrete (RepF FTKScalar (RepN $ fromIntegral i))
        asts :: AstIxS AstMethodLet sh
        asts = let i :: AstInt AstMethodLet
                   i = toLinearIdxS @sh2 @'[] fromInt shOut ix
               in simplifyAstIxS $ fromLinearIdxS fromInt shIn i
                    -- we generate these, so we simplify
    in gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh) $
       gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[]) $
       astGatherKnobsS @sh2 @'[] @sh knobs ZSS v (vars, asts)


-- * Permutation-related operations

--  map fst $ dropWhileEnd (uncurry (==)) $ zip perm [0 ..]
-- TODO: port to shaped permutations and then remove the Hack suffix
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


-- * The simplifying combinators, one for almost each AST constructor

astPair :: AstTensor AstMethodLet s x -> AstTensor AstMethodLet s y
        -> AstTensor AstMethodLet s (TKProduct x y)
-- TODO, but maybe not the best idea?:
-- astPair (Ast.AstConcrete v1) (Ast.AstConcrete v2) =
--   Ast.AstConcrete (v1, v2)
astPair (Ast.AstFromPrimal v1) (Ast.AstFromPrimal v2) =
  Ast.AstFromPrimal $ astPair v1 v2
astPair (Ast.AstFromDual v1) (Ast.AstFromDual v2) =
  Ast.AstFromDual $ astPair v1 v2
astPair (Ast.AstFromS stkz1 v1) (Ast.AstFromS stkz2 v2) =
  astFromS (STKProduct stkz1 stkz2) $ astPair v1 v2
astPair (Ast.AstFromS stkz1 v1) v2 =
  astFromS (STKProduct stkz1 (ftkToSTK (ftkAst v2))) $ astPair v1 v2
astPair v1 (Ast.AstFromS stkz2 v2) =
  astFromS (STKProduct (ftkToSTK (ftkAst v1)) stkz2) $ astPair v1 v2
astPair v1 v2 = Ast.AstPair v1 v2

astProject1
  :: forall x z s. AstSpan s
  => AstTensor AstMethodLet s (TKProduct x z) -> AstTensor AstMethodLet s x
astProject1 u = case u of
  Ast.AstPair x _z -> x
  Ast.AstCond b v1 v2 -> Ast.AstCond b (astProject1 v1) (astProject1 v2)
  Ast.AstConcrete (RepF (FTKProduct ftk1 _ftk2) v) ->
    astConcrete (RepF ftk1 (tproject1 v))
  Ast.AstLet var t v -> Ast.AstLet var t (astProject1 v)
  Ast.AstFromPrimal u1 -> Ast.AstFromPrimal $ astProject1 u1
  Ast.AstFromDual u1 -> Ast.AstFromDual $ astProject1 u1
  Ast.AstFromS (STKProduct stk1 _) u1 | FTKProduct{} <- ftkAst u1 ->
    astFromS stk1 $ astProject1 u1
  _ -> Ast.AstProject1 u

astProject2
  :: forall x z s. AstSpan s
  => AstTensor AstMethodLet s (TKProduct x z) -> AstTensor AstMethodLet s z
astProject2 u = case u of
  Ast.AstPair _x z -> z
  Ast.AstCond b v1 v2 -> Ast.AstCond b (astProject2 v1) (astProject2 v2)
  Ast.AstConcrete (RepF (FTKProduct _ftk1 ftk2) v) ->
    astConcrete (RepF ftk2 (tproject2 v))
  Ast.AstLet var t v -> Ast.AstLet var t (astProject2 v)
  Ast.AstFromPrimal u1 -> Ast.AstFromPrimal $ astProject2 u1
  Ast.AstFromDual u1 -> Ast.AstFromDual $ astProject2 u1
  Ast.AstFromS (STKProduct _ stk2) u1 | FTKProduct{} <- ftkAst u1 ->
    astFromS stk2 $ astProject2 u1
  _ -> Ast.AstProject2 u

astFromVector :: forall y k s. AstSpan s
              => SNat k -> STensorKind y
              -> Data.Vector.Vector (AstTensor AstMethodLet s y)
              -> AstTensor AstMethodLet s (BuildTensorKind k y)
astFromVector snat stk v | Just Refl <- testEquality snat (SNat @1) =
  astReplicate (SNat @1) stk (v V.! 0)
astFromVector snat@SNat stk l = fromMaybe (Ast.AstFromVector snat stk l) $
  (case sameAstSpan @s @PrimalSpan of
     Just Refl ->
       let unConc :: AstTensor AstMethodLet PrimalSpan y
                  -> Maybe (RepF y)
           unConc (AstConcrete repF) = Just repF
           unConc _ = Nothing
       in case V.mapM unConc l of
         Just l4 | V.null l4 -> error "astFromVector: empty vector"
         Just l4 ->
           let l3 = V.map (\(RepF _ a) -> a) l4
               RepF ftk _ = l4 V.! 0
           in Just $ astConcrete (RepF (buildFTK snat ftk)
                                       (tfromVector snat stk l3))
         Nothing -> Nothing
     _ -> Nothing)
  `mplus`
  (case sameAstSpan @s @FullSpan of
     Just Refl ->
       let unFromPrimal :: AstTensor AstMethodLet FullSpan y
                        -> Maybe (AstTensor AstMethodLet PrimalSpan y)
           unFromPrimal (Ast.AstFromPrimal t) = Just t
           unFromPrimal _ = Nothing
       in case V.mapM unFromPrimal l of
         Just l2 | V.null l2 -> error "astFromVector: empty vector"
         Just l2 -> Just $ Ast.AstFromPrimal $ astFromVector snat stk l2
         Nothing -> Nothing
     _ -> Nothing)
  `mplus`
  (case sameAstSpan @s @FullSpan of
     Just Refl ->
       let unFromDual :: AstTensor AstMethodLet FullSpan y
                        -> Maybe (AstTensor AstMethodLet DualSpan y)
           unFromDual (Ast.AstFromDual t) = Just t
           unFromDual _ = Nothing
       in case V.mapM unFromDual l of
         Just l2 | V.null l2 -> error "astFromVector: empty vector"
         Just l2 -> Just $ Ast.AstFromDual $ astFromVector snat stk l2
         Nothing -> Nothing
     _ -> Nothing)
  `mplus`
  (let unFrom :: FullTensorKind x
              -> AstTensor AstMethodLet s y
              -> Maybe (AstTensor AstMethodLet s x)
       unFrom ftkx (Ast.AstFromS _ t) =
         case matchingFTK (ftkAst t) ftkx of
           Just Refl -> Just t
           Nothing -> error "astFromVector: impossible shape"
       unFrom _ _ = Nothing
   in case V.uncons l of
     Just (Ast.AstFromS stkz v, _) ->
       case V.mapM (unFrom (ftkAst v)) l of
         Just l2 ->
           Just $ astFromS (buildSTK snat stkz)
                $ astFromVector snat (ftkToSTK (ftkAst v)) l2
         Nothing -> Nothing
     Just{} -> Nothing
     Nothing -> error "astFromVector: empty vector")

astSum :: forall y k s. AstSpan s
       => SNat k -> STensorKind y
       -> AstTensor AstMethodLet s (BuildTensorKind k y)
       -> AstTensor AstMethodLet s y
astSum snat@SNat stk t0 = case t0 of
--  1 :$: rest -> astReshape rest t0  -- TODO: slows down the CNNO test
  _ | Just Refl <- testEquality snat (SNat @0) ->
    let ftk = razeFTK snat stk (ftkAst t0)
    in fromPrimal $ astConcrete (RepF ftk (tconstantTarget 0 ftk))
  Ast.AstFromVector @y2 _ _ l ->
    gcastWith (unsafeCoerceRefl :: y2 :~: y) $
    case stk of
      STKScalar -> astSumOfList $ NonEmpty.fromList $ V.toList l
      STKR _ STKScalar -> astSumOfList $ NonEmpty.fromList $ V.toList l
      STKS _ STKScalar -> astSumOfList $ NonEmpty.fromList $ V.toList l
      STKX _ STKScalar -> astSumOfList $ NonEmpty.fromList $ V.toList l
      _ -> Ast.AstSum snat stk t0
  Ast.AstReplicate _ STKScalar v | STKScalar <- stk ->
    let ftk = FTKScalar
    in v * (fromPrimal
            $ astConcrete (RepF ftk (tconstantTarget (fromInteger
                                                      $ fromSNat snat) ftk)))
  Ast.AstReplicate _ _ v | STKR _ (STKScalar @r) <- stk ->
    case ftkAst v of
      FTKR sh' FTKScalar ->
        withCastRS sh' $ \(sh :: ShS sh) ->
          let ftk = FTKS sh (FTKScalar @r)
          in v * astFromS stk (fromPrimal
                               $ astConcrete (RepF ftk
                                                   (tconstantTarget
                                                      (fromInteger
                                                       $ fromSNat snat) ftk)))
  Ast.AstReplicate _ _ v | STKX _ (STKScalar @r) <- stk ->
    case ftkAst v of
      FTKX sh' FTKScalar ->
        withCastXS sh' $ \(sh :: ShS sh) ->
          let ftk = FTKS sh (FTKScalar @r)
          in v * astFromS stk (fromPrimal
                               $ astConcrete (RepF ftk
                                                   (tconstantTarget
                                                      (fromInteger
                                                       $ fromSNat snat) ftk)))
  Ast.AstReplicate _ STKS{} v | STKS sh (STKScalar @r) <- stk ->
    let ftk = FTKS sh (FTKScalar @r)
    in v * (fromPrimal $ astConcrete (RepF ftk
                                           (tconstantTarget
                                              (fromInteger
                                               $ fromSNat snat) ftk)))
  AstConcrete (RepF ftk t) ->
    astConcrete (RepF (razeFTK snat stk ftk) (tsum snat stk t))
  -- Ast.AstLet var u v -> astLet var u (astSum snat v)
    -- this is problematic, because it keeps huge tensors alive for longer
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astSum snat stk v
  Ast.AstFromDual v -> Ast.AstFromDual $ astSum snat stk v
  {- TODO: this requires a check that the eliminated index is in bounds:
  Ast.AstScatterS @shm @shn @shp v (vars, _ :.$ ix)
    | STKS{} <- stk ->
      astScatterS @shm @shn @(Tail shp) v (vars, ix) -}
  Ast.AstSliceS (SNat @i) n SNat v | STKS sh _ <- stk
                                   , Just Refl <- sameNat n (SNat @1) ->
    astIndexS sh v (valueOf @i :.$ ZIS)
  Ast.AstReverseS v -> astSum snat stk v
  Ast.AstFromS _ v -> case ftkToSTK (ftkAst v) of
    STKS (snat2 :$$ rest) x -> astFromS stk $ astSum snat2 (STKS rest x) v
    _ -> Ast.AstSum snat stk t0  -- products probably not worth the effort
  _ -> Ast.AstSum snat stk t0

astReplicate :: forall y k s. AstSpan s
             => SNat k -> STensorKind y
             -> AstTensor AstMethodLet s y
             -> AstTensor AstMethodLet s (BuildTensorKind k y)
astReplicate snat@SNat stk = \case
-- This allocates a big tensor too early, while it's still possible
-- a projection reduces this away. The cost to AD should not be too high.
-- This would also hide AstReplicate from hacks that recover tmatmul2, etc.
--  AstConcrete t -> astConcrete $ treplicateR k t
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astReplicate snat stk v
  Ast.AstFromDual v -> Ast.AstFromDual $ astReplicate snat stk v
{- TODO: these may be counterproductive with many gathers and their fusion
         though these let transpose cancel out with each other sometimes
         (instead we should try to cancel out inside replicate and only move
          if they don't) -}
  Ast.AstTransposeS @perm @sh1 perm v -> case stk of
    STKS @sh _ _ ->
      let zsuccPerm :: Permutation.Perm (0 : Permutation.MapSucc perm)
          zsuccPerm = Permutation.permShift1 perm
      in
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix (0 : Permutation.MapSucc perm)
                                                (k : sh1) :~: k : sh) $
        gcastWith (unsafeCoerceRefl
                   :: Rank (0 : Permutation.MapSucc perm) :~: 1 + Rank perm) $
        trustMeThisIsAPermutation @(0 : Permutation.MapSucc perm) $
        astTransposeS zsuccPerm $ astReplicate snat (ftkToSTK (ftkAst v)) v
{- see the previous comment
  Ast.AstReshape sh v ->
    AstReshape (k :$: sh) $ astReplicate k v
-}
  Ast.AstFromS stkz v ->
    astFromS (buildSTK snat stkz) $ astReplicate snat (ftkToSTK (ftkAst v)) v
  v -> Ast.AstReplicate snat stk v

-- TODO: also push up AstFromPrimal, etc.
astMapAccumRDer
  :: forall accShs bShs eShs k s.
     SNat k
  -> FullTensorKind bShs
  -> FullTensorKind eShs
  -> AstHFun (TKProduct accShs eShs) (TKProduct accShs bShs)
  -> AstHFun (TKProduct (ADTensorKind (TKProduct accShs eShs))
                        (TKProduct accShs eShs))
             (ADTensorKind (TKProduct accShs bShs))
  -> AstHFun (TKProduct (ADTensorKind (TKProduct accShs bShs))
                        (TKProduct accShs eShs))
             (ADTensorKind (TKProduct accShs eShs))
  -> AstTensor AstMethodLet s accShs
  -> AstTensor AstMethodLet s (BuildTensorKind k eShs)
  -> AstTensor AstMethodLet s (TKProduct accShs (BuildTensorKind k bShs))
astMapAccumRDer k bShs eShs (AstLambda (varf, _ftkf, vf))
                            (AstLambda (vard, _ftkd, vd))
                            (AstLambda (varr, _ftkr, vr))
                (Ast.AstFromS @accShsFrom accShsSTK acc0From) es =
  let accShsFrom = ftkAst acc0From
      accShsFromSTK = ftkToSTK accShsFrom
      ftkf2 = FTKProduct accShsFrom eShs
      varf2 = mkAstVarName (ftkToSTK ftkf2) (varNameToAstVarId varf)
      astf2 = Ast.AstVar ftkf2 varf2
      vf2 =
        let subbed =
              substituteAst
                (astPair (astFromS @accShsFrom accShsSTK (astProject1 astf2))
                         (astProject2 astf2))
                varf vf
        in astSFrom @(TKProduct accShs bShs)
                    (STKProduct accShsFromSTK (ftkToSTK bShs))
                    subbed
      ftkd2 = FTKProduct
                (adFTK $ FTKProduct accShsFrom eShs)
                (FTKProduct accShsFrom eShs)
      vard2 = mkAstVarName (ftkToSTK ftkd2) (varNameToAstVarId vard)
      astd2 = Ast.AstVar ftkd2 vard2
      vd2 =
        let subbed =
              substituteAst
                (astPair (astPair (astFromS @(ADTensorKind accShsFrom)
                                     (adSTK accShsSTK)
                                     (astProject1 (astProject1 astd2)))
                                  (astProject2 (astProject1 astd2)))
                         (astPair (astFromS @accShsFrom accShsSTK
                                     (astProject1 (astProject2 astd2)))
                                  (astProject2 (astProject2 astd2))))
                vard vd
        in astSFrom @(ADTensorKind (TKProduct accShs bShs))
                    (adSTK $ STKProduct accShsFromSTK (ftkToSTK bShs))
                    subbed
      ftkr2 = FTKProduct
                (adFTK $ FTKProduct accShsFrom bShs)
                (FTKProduct accShsFrom eShs)
      varr2 = mkAstVarName (ftkToSTK ftkr2) (varNameToAstVarId varr)
      astr2 = Ast.AstVar ftkr2 varr2
      vr2 =
        let subbed =
              substituteAst
                (astPair (astPair (astFromS @(ADTensorKind accShsFrom)
                                     (adSTK accShsSTK)
                                     (astProject1 (astProject1 astr2)))
                                  (astProject2 (astProject1 astr2)))
                         (astPair (astFromS @accShsFrom accShsSTK
                                     (astProject1 (astProject2 astr2)))
                                  (astProject2 (astProject2 astr2))))
                varr vr
        in astSFrom @(ADTensorKind (TKProduct accShs eShs))
                    (adSTK $ STKProduct accShsFromSTK (ftkToSTK eShs))
                    subbed
  in astFromS @(TKProduct accShsFrom (BuildTensorKind k bShs))
              (STKProduct accShsSTK (buildSTK k (ftkToSTK bShs)))
     $ astMapAccumRDer k bShs eShs (AstLambda (varf2, ftkf2, vf2))
                                   (AstLambda (vard2, ftkd2, vd2))
                                   (AstLambda (varr2, ftkr2, vr2))
                                   acc0From es
astMapAccumRDer k bShs eShs (AstLambda (varf, _ftkf, vf))
                            (AstLambda (vard, _ftkd, vd))
                            (AstLambda (varr, _ftkr, vr))
                acc0 (Ast.AstFromS @esShsFrom _esShsSTK esFrom) =
  let accShs = ftkAst acc0
      accShsSTK = ftkToSTK accShs
      esShsFrom = ftkAst esFrom
      esShsFromSTK = ftkToSTK esShsFrom
  in case razeSTK esShsFromSTK of
    (eShsFromSTK :: STensorKind eShsFrom) ->
      gcastWith (unsafeCoerceRefl
                 :: BuildTensorKind k eShsFrom :~: esShsFrom) $
      let eShsFrom = razeFTK k eShsFromSTK esShsFrom
          ftkf2 = FTKProduct accShs eShsFrom
          varf2 = mkAstVarName (ftkToSTK ftkf2) (varNameToAstVarId varf)
          astf2 = Ast.AstVar ftkf2 varf2
          vf2 =
            let subbed =
                  substituteAst
                    (astPair (astProject1 astf2)
                             (astFromS @eShsFrom
                                (ftkToSTK eShs) (astProject2 astf2)))
                    varf vf
            in subbed
          ftkd2 = FTKProduct
                    (adFTK $ FTKProduct accShs eShsFrom)
                    (FTKProduct accShs eShsFrom)
          vard2 = mkAstVarName (ftkToSTK ftkd2) (varNameToAstVarId vard)
          astd2 = Ast.AstVar ftkd2 vard2
          vd2 =
            let subbed =
                  substituteAst
                    (astPair (astPair (astProject1 (astProject1 astd2))
                                      (astFromS @(ADTensorKind eShsFrom)
                                         (adSTK (ftkToSTK eShs))
                                         (astProject2 (astProject1 astd2))))
                             (astPair (astProject1 (astProject2 astd2))
                                      (astFromS @eShsFrom (ftkToSTK eShs)
                                         (astProject2 (astProject2 astd2)))))
                    vard vd
            in subbed
          ftkr2 = FTKProduct
                    (adFTK $ FTKProduct accShs bShs)
                    (FTKProduct accShs eShsFrom)
          varr2 = mkAstVarName (ftkToSTK ftkr2) (varNameToAstVarId varr)
          astr2 = Ast.AstVar ftkr2 varr2
          vr2 =
            let subbed =
                  substituteAst
                    (astPair (astProject1 astr2)
                             (astPair (astProject1 (astProject2 astr2))
                                      (astFromS @eShsFrom (ftkToSTK eShs)
                                         (astProject2 (astProject2 astr2)))))
                    varr vr
            in astSFrom @(ADTensorKind (TKProduct accShs eShs))
                        (adSTK $ STKProduct accShsSTK eShsFromSTK)
                        subbed
      in astMapAccumRDer k bShs eShsFrom (AstLambda (varf2, ftkf2, vf2))
                                         (AstLambda (vard2, ftkd2, vd2))
                                         (AstLambda (varr2, ftkr2, vr2))
                                         acc0 esFrom
astMapAccumRDer k bShs eShs f df rf acc0 es =
  Ast.AstMapAccumRDer k bShs eShs f df rf acc0 es

astMapAccumLDer
  :: forall accShs bShs eShs k s.
     SNat k
  -> FullTensorKind bShs
  -> FullTensorKind eShs
  -> AstHFun (TKProduct accShs eShs) (TKProduct accShs bShs)
  -> AstHFun (TKProduct (ADTensorKind (TKProduct accShs eShs))
                        (TKProduct accShs eShs))
             (ADTensorKind (TKProduct accShs bShs))
  -> AstHFun (TKProduct (ADTensorKind (TKProduct accShs bShs))
                        (TKProduct accShs eShs))
             (ADTensorKind (TKProduct accShs eShs))
  -> AstTensor AstMethodLet s accShs
  -> AstTensor AstMethodLet s (BuildTensorKind k eShs)
  -> AstTensor AstMethodLet s (TKProduct accShs (BuildTensorKind k bShs))
astMapAccumLDer k bShs eShs (AstLambda (varf, _ftkf, vf))
                            (AstLambda (vard, _ftkd, vd))
                            (AstLambda (varr, _ftkr, vr))
                (Ast.AstFromS @accShsFrom accShsSTK acc0From) es =
  let accShsFrom = ftkAst acc0From
      accShsFromSTK = ftkToSTK accShsFrom
      ftkf2 = FTKProduct accShsFrom eShs
      varf2 = mkAstVarName (ftkToSTK ftkf2) (varNameToAstVarId varf)
      astf2 = Ast.AstVar ftkf2 varf2
      vf2 =
        let subbed =
              substituteAst
                (astPair (astFromS @accShsFrom accShsSTK (astProject1 astf2))
                         (astProject2 astf2))
                varf vf
        in astSFrom @(TKProduct accShs bShs)
                    (STKProduct accShsFromSTK (ftkToSTK bShs))
                    subbed
      ftkd2 = FTKProduct
                (adFTK $ FTKProduct accShsFrom eShs)
                (FTKProduct accShsFrom eShs)
      vard2 = mkAstVarName (ftkToSTK ftkd2) (varNameToAstVarId vard)
      astd2 = Ast.AstVar ftkd2 vard2
      vd2 =
        let subbed =
              substituteAst
                (astPair (astPair (astFromS @(ADTensorKind accShsFrom)
                                     (adSTK accShsSTK)
                                     (astProject1 (astProject1 astd2)))
                                  (astProject2 (astProject1 astd2)))
                         (astPair (astFromS @accShsFrom accShsSTK
                                     (astProject1 (astProject2 astd2)))
                                  (astProject2 (astProject2 astd2))))
                vard vd
        in astSFrom @(ADTensorKind (TKProduct accShs bShs))
                    (adSTK $ STKProduct accShsFromSTK (ftkToSTK bShs))
                    subbed
      ftkr2 = FTKProduct
                (adFTK $ FTKProduct accShsFrom bShs)
                (FTKProduct accShsFrom eShs)
      varr2 = mkAstVarName (ftkToSTK ftkr2) (varNameToAstVarId varr)
      astr2 = Ast.AstVar ftkr2 varr2
      vr2 =
        let subbed =
              substituteAst
                (astPair (astPair (astFromS @(ADTensorKind accShsFrom)
                                     (adSTK accShsSTK)
                                     (astProject1 (astProject1 astr2)))
                                  (astProject2 (astProject1 astr2)))
                         (astPair (astFromS @accShsFrom accShsSTK
                                     (astProject1 (astProject2 astr2)))
                                  (astProject2 (astProject2 astr2))))
                varr vr
        in astSFrom @(ADTensorKind (TKProduct accShs eShs))
                    (adSTK $ STKProduct accShsFromSTK (ftkToSTK eShs))
                    subbed
  in astFromS @(TKProduct accShsFrom (BuildTensorKind k bShs))
              (STKProduct accShsSTK (buildSTK k (ftkToSTK bShs)))
     $ astMapAccumLDer k bShs eShs (AstLambda (varf2, ftkf2, vf2))
                                   (AstLambda (vard2, ftkd2, vd2))
                                   (AstLambda (varr2, ftkr2, vr2))
                                   acc0From es
astMapAccumLDer k bShs eShs (AstLambda (varf, _ftkf, vf))
                            (AstLambda (vard, _ftkd, vd))
                            (AstLambda (varr, _ftkr, vr))
                acc0 (Ast.AstFromS @esShsFrom _esShsSTK esFrom) =
  let accShs = ftkAst acc0
      accShsSTK = ftkToSTK accShs
      esShsFrom = ftkAst esFrom
      esShsFromSTK = ftkToSTK esShsFrom
  in case razeSTK esShsFromSTK of
    (eShsFromSTK :: STensorKind eShsFrom) ->
      gcastWith (unsafeCoerceRefl
                 :: BuildTensorKind k eShsFrom :~: esShsFrom) $
      let eShsFrom = razeFTK k eShsFromSTK esShsFrom
          ftkf2 = FTKProduct accShs eShsFrom
          varf2 = mkAstVarName (ftkToSTK ftkf2) (varNameToAstVarId varf)
          astf2 = Ast.AstVar ftkf2 varf2
          vf2 =
            let subbed =
                  substituteAst
                    (astPair (astProject1 astf2)
                             (astFromS @eShsFrom
                                (ftkToSTK eShs) (astProject2 astf2)))
                    varf vf
            in subbed
          ftkd2 = FTKProduct
                    (adFTK $ FTKProduct accShs eShsFrom)
                    (FTKProduct accShs eShsFrom)
          vard2 = mkAstVarName (ftkToSTK ftkd2) (varNameToAstVarId vard)
          astd2 = Ast.AstVar ftkd2 vard2
          vd2 =
            let subbed =
                  substituteAst
                    (astPair (astPair (astProject1 (astProject1 astd2))
                                      (astFromS @(ADTensorKind eShsFrom)
                                         (adSTK (ftkToSTK eShs))
                                         (astProject2 (astProject1 astd2))))
                             (astPair (astProject1 (astProject2 astd2))
                                      (astFromS @eShsFrom (ftkToSTK eShs)
                                         (astProject2 (astProject2 astd2)))))
                    vard vd
            in subbed
          ftkr2 = FTKProduct
                    (adFTK $ FTKProduct accShs bShs)
                    (FTKProduct accShs eShsFrom)
          varr2 = mkAstVarName (ftkToSTK ftkr2) (varNameToAstVarId varr)
          astr2 = Ast.AstVar ftkr2 varr2
          vr2 =
            let subbed =
                  substituteAst
                    (astPair (astProject1 astr2)
                             (astPair (astProject1 (astProject2 astr2))
                                      (astFromS @eShsFrom (ftkToSTK eShs)
                                         (astProject2 (astProject2 astr2)))))
                    varr vr
            in astSFrom @(ADTensorKind (TKProduct accShs eShs))
                        (adSTK $ STKProduct accShsSTK eShsFromSTK)
                        subbed
      in astMapAccumLDer k bShs eShsFrom (AstLambda (varf2, ftkf2, vf2))
                                         (AstLambda (vard2, ftkd2, vd2))
                                         (AstLambda (varr2, ftkr2, vr2))
                                         acc0 esFrom
astMapAccumLDer k bShs eShs f df rf acc0 es =
  Ast.AstMapAccumLDer k bShs eShs f df rf acc0 es

astApply :: forall s x z. AstSpan s
         => STensorKind z -> AstHFun x z -> AstTensor AstMethodLet s x
         -> AstTensor AstMethodLet s z
astApply stk t u = case t of
  Ast.AstLambda ~(var, _ftk, v) ->
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> astLet var u v
      _ -> Ast.AstApply stk t u

astCond :: AstBool AstMethodLet
        -> AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
        -> AstTensor AstMethodLet s y
astCond (AstBoolConst b) v w = if b then v else w
astCond b (Ast.AstFromPrimal v) (Ast.AstFromPrimal w) =
  Ast.AstFromPrimal $ astCond b v w
astCond b (Ast.AstFromDual v) (Ast.AstFromDual w) =
  Ast.AstFromDual $ astCond b v w
astCond b (Ast.AstFromS stkzv v) (Ast.AstFromS _ w) =
  case matchingFTK (ftkAst v) (ftkAst w) of
    Just Refl -> astFromS stkzv $ astCond b v w
    Nothing -> error "astCond: shapes don't match"
astCond b v w = Ast.AstCond b v w

astConcrete :: RepF y -> AstTensor AstMethodLet PrimalSpan y
astConcrete (RepF ftk v) = case ftk of
  FTKR sh' x | SNat <- shrRank sh'
             , Dict <- lemKnownSTK (ftkToSTK x) ->
    withCastRS sh' $ \sh ->
      withKnownShS sh $
      astFromS (ftkToSTK ftk) $ AstConcrete (RepF (FTKS sh x) (sfromR v))
  FTKX sh' x | Dict <- lemKnownSTK (ftkToSTK x) ->
    withCastXS sh' $ \sh ->
      withKnownShX (ssxFromShape sh') $
      withKnownShS sh $
      astFromS (ftkToSTK ftk) $ AstConcrete (RepF (FTKS sh x) (sfromX v))
  _ -> AstConcrete (RepF ftk v)  -- product case should be too rare to care

-- Inlining works for this let constructor, because it has just one variable,
-- unlike astLetHVectorIn, etc., so we don't try to eliminate it.
astLet :: forall y z s s2. (AstSpan s, AstSpan s2)
       => AstVarName s y -> AstTensor AstMethodLet s y
       -> AstTensor AstMethodLet s2 z
       -> AstTensor AstMethodLet s2 z
astLet _var _u v@Ast.AstConcrete{} = v
astLet var u v | astIsSmall True u =
  substituteAst u var v
astLet var (Ast.AstPair u1 u2) v =
  astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
    substituteAst (Ast.AstPair ast1 ast2) var v
astLet var (Ast.AstFromPrimal (Ast.AstPair u1 u2)) v =
  astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
    substituteAst (Ast.AstFromPrimal (Ast.AstPair ast1 ast2)) var v
astLet var (Ast.AstFromDual (Ast.AstPair u1 u2)) v =
  astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
    substituteAst (Ast.AstFromDual (Ast.AstPair ast1 ast2)) var v
astLet var (Ast.AstLet varN uN (Ast.AstPair u1 u2)) v =
  astLet varN uN
  $ astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
      substituteAst ( Ast.AstPair ast1 ast2) var v
astLet var (Ast.AstFromPrimal (Ast.AstLet varN uN (Ast.AstPair u1 u2))) v =
  astLet varN uN
  $ astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
      substituteAst (Ast.AstFromPrimal (Ast.AstPair ast1 ast2)) var v
astLet var (Ast.AstFromDual (Ast.AstLet varN uN (Ast.AstPair u1 u2))) v =
  astLet varN uN
  $ astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
      substituteAst (Ast.AstFromDual (Ast.AstPair ast1 ast2)) var v
astLet var u v@(Ast.AstVar _ var2) =
  if varNameToAstVarId var2 == varNameToAstVarId var
  then case sameAstSpan @s @s2 of
    Just Refl -> case sameSTK (varNameToSTK var) (varNameToSTK var2) of
      Just Refl -> u
      _ -> v
    _ -> v
  else v
astLet var u v@(Ast.AstPrimalPart (Ast.AstVar _ var2)) =  -- a common noop
  if varNameToAstVarId var2 == varNameToAstVarId var
  then case sameAstSpan @s @FullSpan of
    Just Refl -> case sameSTK (varNameToSTK var) (varNameToSTK var2) of
      Just Refl -> astPrimalPart u
      _ -> v
    _ -> v
  else v
astLet var u v@(Ast.AstDualPart (Ast.AstVar _ var2)) =  -- a noop
  if varNameToAstVarId var2 == varNameToAstVarId var
  then case sameAstSpan @s @FullSpan of
    Just Refl -> case sameSTK (varNameToSTK var) (varNameToSTK var2) of
      Just Refl -> astDualPart u
      _ -> v
    _ -> v
  else v
astLet var u (Ast.AstFromPrimal v0) = Ast.AstFromPrimal $ astLet var u v0
astLet var u (Ast.AstFromDual v0) = Ast.AstFromDual $ astLet var u v0
astLet var u (Ast.AstFromS stkz v) =
  astFromS stkz $ astLet var u v
astLet var (Ast.AstFromS stkz a) v =
  let var2 = mkAstVarName (ftkToSTK (ftkAst a)) (varNameToAstVarId var)
      ast = astFromS stkz $ Ast.AstVar (ftkAst a) var2
  in astLet var2 a (substituteAst ast var v)
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

astPrimalPart :: AstTensor AstMethodLet FullSpan y
              -> AstTensor AstMethodLet PrimalSpan y
astPrimalPart t = case t of
  Ast.AstPair t1 t2 -> astPair (astPrimalPart t1) (astPrimalPart t2)
  Ast.AstProject1 v -> astProject1 (astPrimalPart v)
  Ast.AstProject2 v -> astProject2 (astPrimalPart v)
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map astPrimalPart l)
  Ast.AstSum snat stk v ->
    astSum snat stk (astPrimalPart v)
  Ast.AstReplicate snat stk v ->
    astReplicate snat stk (astPrimalPart v)
  Ast.AstMapAccumRDer k bShs eShs f df rf acc0 es ->
      astMapAccumRDer k bShs eShs f df rf
                      (astPrimalPart acc0) (astPrimalPart es)
  Ast.AstMapAccumLDer k bShs eShs f df rf acc0 es ->
      astMapAccumLDer k bShs eShs f df rf
                      (astPrimalPart acc0) (astPrimalPart es)
  Ast.AstApply stk v ll -> astApply stk v (astPrimalPart ll)
  Ast.AstVar{} -> Ast.AstPrimalPart t  -- the only normal form
  Ast.AstCond b a2 a3 -> astCond b (astPrimalPart a2) (astPrimalPart a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = astPrimalPart v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var u (astPrimalPart v)

  Ast.AstFromPrimal v -> v
  Ast.AstFromDual v ->
    let ftk = ftkAst v
    in astConcrete (RepF ftk (tconstantTarget 0 ftk))

  AstSumOfList args -> astSumOfList (NonEmpty.map astPrimalPart args)

  AstN1K opCode u -> AstN1K opCode (astPrimalPart u)
  AstN2K opCode u v -> AstN2K opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (astPrimalPart u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2K opCode u v -> Ast.AstI2K opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstCastK v -> astCastK $ astPrimalPart v

  AstN1S opCode u -> AstN1S opCode (astPrimalPart u)
  AstN2S opCode u v -> AstN2S opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astPrimalPart u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (astPrimalPart u)
                                             (astPrimalPart v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (astPrimalPart u)
                                             (astPrimalPart v)
  Ast.AstCastS v -> astCastS $ astPrimalPart v

  Ast.AstIndexS shn v ix ->
    astIndexS shn (astPrimalPart v) ix
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    astScatterS @shm @shn @shp shn (astPrimalPart v) (vars, ix)
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    astGatherS @shm @shn @shp shn (astPrimalPart v) (vars, ix)
  Ast.AstAppendS x y -> astAppendS (astPrimalPart x) (astPrimalPart y)
  Ast.AstSliceS i n k v -> astSliceS i n k (astPrimalPart v)
  Ast.AstReverseS v -> astReverseS (astPrimalPart v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astPrimalPart v)
  Ast.AstReshapeS sh v -> astReshapeS sh (astPrimalPart v)
  Ast.AstZipS v -> Ast.AstZipS (astPrimalPart v)
  Ast.AstUnzipS v -> Ast.AstUnzipS (astPrimalPart v)
  Ast.AstNestS sh1 sh2 v ->
    astNestS sh1 sh2 $ astPrimalPart v
  Ast.AstUnNestS v -> astUnNestS $ astPrimalPart v

  Ast.AstFromS stkz v ->
    astFromS stkz $ astPrimalPart v
  -- These conversions need to stay down.
  Ast.AstSFromK{} -> Ast.AstPrimalPart t
  Ast.AstSFromR{} -> Ast.AstPrimalPart t
  Ast.AstSFromX{} -> Ast.AstPrimalPart t

  -- These should not appear in this context unless via wacky tests.
  Ast.AstReplicate0NS{} -> Ast.AstPrimalPart t
  Ast.AstSum0S{} -> Ast.AstPrimalPart t
  Ast.AstDot0S{} -> Ast.AstPrimalPart t
  Ast.AstDot1InS{} -> Ast.AstPrimalPart t
  Ast.AstMatvecmulS{} -> Ast.AstPrimalPart t
  Ast.AstMatmul2S{} -> Ast.AstPrimalPart t

-- Note how this can't be pushed down, say, multiplication, because it
-- multiplies the dual part by the primal part. Addition is fine, though.
astDualPart :: AstTensor AstMethodLet FullSpan y
            -> AstTensor AstMethodLet DualSpan y
astDualPart t = case t of
  Ast.AstPair t1 t2 -> astPair (astDualPart t1) (astDualPart t2)
  Ast.AstProject1 v -> astProject1 (astDualPart v)
  Ast.AstProject2 v -> astProject2 (astDualPart v)
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map astDualPart l)
  Ast.AstSum snat stk v ->
    astSum snat stk (astDualPart v)
  Ast.AstReplicate snat stk v ->
    astReplicate snat stk (astDualPart v)
  Ast.AstMapAccumRDer k bShs eShs f df rf acc0 es ->
      astMapAccumRDer k bShs eShs f df rf
                      (astDualPart acc0) (astDualPart es)
  Ast.AstMapAccumLDer k bShs eShs f df rf acc0 es ->
      astMapAccumLDer k bShs eShs f df rf
                      (astDualPart acc0) (astDualPart es)
  Ast.AstApply stk v ll -> astApply stk v (astDualPart ll)
  Ast.AstVar{} -> Ast.AstDualPart t  -- the only normal form
  Ast.AstCond b a2 a3 -> astCond b (astDualPart a2) (astDualPart a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = astDualPart v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var u (astDualPart v)

  Ast.AstFromPrimal{} -> Ast.AstDualPart t  -- TODO: replace t with something small
  Ast.AstFromDual v -> v

  AstSumOfList args -> astSumOfList (NonEmpty.map astDualPart args)

  AstN1K opCode u -> AstN1K opCode (astDualPart u)
  AstN2K opCode u v -> AstN2K opCode (astDualPart u) (astDualPart v)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (astDualPart u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (astDualPart u) (astDualPart v)
  Ast.AstI2K opCode u v -> Ast.AstI2K opCode (astDualPart u) (astDualPart v)
  Ast.AstCastK v -> astCastK $ astDualPart v

  AstN1S opCode u -> AstN1S opCode (astDualPart u)
  AstN2S opCode u v -> AstN2S opCode (astDualPart u) (astDualPart v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astDualPart u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (astDualPart u)
                                             (astDualPart v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (astDualPart u)
                                             (astDualPart v)
  Ast.AstCastS v -> astCastS $ astDualPart v

  Ast.AstIndexS shn v ix ->
    astIndexS shn (astDualPart v) ix
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    astScatterS @shm @shn @shp shn (astDualPart v) (vars, ix)
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    astGatherS @shm @shn @shp shn (astDualPart v) (vars, ix)
  Ast.AstAppendS x y -> astAppendS (astDualPart x) (astDualPart y)
  Ast.AstSliceS i n k v -> astSliceS i n k (astDualPart v)
  Ast.AstReverseS v -> astReverseS (astDualPart v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astDualPart v)
  Ast.AstReshapeS sh v -> astReshapeS sh (astDualPart v)
  Ast.AstZipS v -> Ast.AstZipS (astDualPart v)
  Ast.AstUnzipS v -> Ast.AstUnzipS (astDualPart v)
  Ast.AstNestS sh1 sh2 v ->
    astNestS sh1 sh2 $ astDualPart v
  Ast.AstUnNestS v -> astUnNestS $ astDualPart v

  Ast.AstFromS stkz v ->
    astFromS stkz $ astDualPart v
   -- These conversions need to stay down.
  Ast.AstSFromK{} -> Ast.AstDualPart t
  Ast.AstSFromR{} -> Ast.AstDualPart t
  Ast.AstSFromX{} -> Ast.AstDualPart t

  -- These should not appear in this context unless via wacky tests.
  Ast.AstReplicate0NS{} -> Ast.AstDualPart t
  Ast.AstSum0S{} -> Ast.AstDualPart t
  Ast.AstDot0S{} -> Ast.AstDualPart t
  Ast.AstDot1InS{} -> Ast.AstDualPart t
  Ast.AstMatvecmulS{} -> Ast.AstDualPart t
  Ast.AstMatmul2S{} -> Ast.AstDualPart t

astSumOfList :: AstSpan s
             => NonEmpty (AstTensor AstMethodLet s y)
             -> AstTensor AstMethodLet s y
astSumOfList l = case l of
  a :| _ -> case ftkToSTK (ftkAst a) of
    STKScalar -> foldr1 (+) l  -- @sum@ breaks and also reverses order
    STKR _ STKScalar -> foldr1 (+) l
    STKS _ STKScalar -> foldr1 (+) l
    STKX _ STKScalar -> foldr1 (+) l
    stk -> let v = V.fromList $ toList l
           in withSNat (V.length v) $ \snat ->
                astSum snat stk $ astFromVector snat stk v

astFromIntegralK :: (GoodScalar r1, GoodScalar r2, Integral r1)
                 => AstTensor AstMethodLet PrimalSpan (TKScalar r1)
                 -> AstTensor AstMethodLet PrimalSpan (TKScalar r2)
astFromIntegralK (AstConcrete (RepF FTKScalar t)) =
  astConcrete (RepF FTKScalar (kfromIntegral t))
astFromIntegralK (Ast.AstFromIntegralK v) = astFromIntegralK v
astFromIntegralK @r1 @r2 v = case testEquality (typeRep @r1) (typeRep @r2) of
  Just Refl -> v
  _ -> Ast.AstFromIntegralK v

astCastK :: (GoodScalar r1, GoodScalar r2, RealFrac r1, RealFrac r2)
         => AstTensor AstMethodLet s (TKScalar r1)
         -> AstTensor AstMethodLet s (TKScalar r2)
astCastK (AstConcrete (RepF FTKScalar t)) =
  astConcrete (RepF FTKScalar (kcast t))
astCastK (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astCastK v
astCastK (Ast.AstFromDual v) = Ast.AstFromDual $ astCastK v
astCastK (Ast.AstFromIntegralK v) = astFromIntegralK v
astCastK (Ast.AstCastK v) = astCastK v
astCastK @r1 @r2 v = case testEquality (typeRep @r1) (typeRep @r2) of
  Just Refl -> v
  _ -> Ast.AstCastK v

astFromIntegralS :: (GoodScalar r1, GoodScalar r2, Integral r1)
                 => AstTensor AstMethodLet PrimalSpan (TKS sh r1)
                 -> AstTensor AstMethodLet PrimalSpan (TKS sh r2)
astFromIntegralS (AstConcrete (RepF (FTKS sh FTKScalar) t)) =
  withKnownShS sh $
  astConcrete (RepF (FTKS sh FTKScalar) (sfromIntegral t))
astFromIntegralS (Ast.AstFromIntegralS v) = astFromIntegralS v
astFromIntegralS @r1 @r2 v = case testEquality (typeRep @r1) (typeRep @r2) of
  Just Refl -> v
  _ -> Ast.AstFromIntegralS v

astCastS :: (GoodScalar r1, GoodScalar r2, RealFrac r1, RealFrac r2)
         => AstTensor AstMethodLet s (TKS sh r1)
         -> AstTensor AstMethodLet s (TKS sh r2)
astCastS (AstConcrete (RepF (FTKS sh FTKScalar) t)) =
  withKnownShS sh $
  astConcrete (RepF (FTKS sh FTKScalar) (scast t))
astCastS (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astCastS v
astCastS (Ast.AstFromDual v) = Ast.AstFromDual $ astCastS v
astCastS (Ast.AstFromIntegralS v) = astFromIntegralS v
astCastS (Ast.AstCastS v) = astCastS v
astCastS @r1 @r2 v = case testEquality (typeRep @r1) (typeRep @r2) of
  Just Refl -> v
  _ -> Ast.AstCastS v

astIndexS
  :: forall shm shn s r. AstSpan s
  => ShS shn
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r) -> AstIxS AstMethodLet shm
  -> AstTensor AstMethodLet s (TKS2 shn r)
astIndexS = astIndexKnobsS defaultKnobs

astIndexStepS
  :: forall shm shn s r. AstSpan s
  => ShS shn
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r) -> AstIxS AstMethodLet shm
  -> AstTensor AstMethodLet s (TKS2 shn r)
astIndexStepS shn v ix =
  astIndexKnobsS (defaultKnobs {knobStepOnly = True})
                 shn
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
astIndexKnobsS
  :: forall shm shn s r. AstSpan s
  => SimplifyKnobs
  -> ShS shn
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
  -> AstIxS AstMethodLet shm
  -> AstTensor AstMethodLet s (TKS2 shn r)
astIndexKnobsS knobs shn (Ast.AstIndexS _ v ix) ZIS =
  astIndexKnobsS knobs shn v ix  -- no non-indexing constructor yet revealed
astIndexKnobsS _ _ v0 ZIS = v0
astIndexKnobsS knobs shn v0 ix@((:.$) @in1 @shm1 i1 rest1) =
 let FTKS _ x = ftkAst v0
     astIndexRec, astIndex
       :: forall shm' shn' s'. AstSpan s'
       => ShS shn'
       -> AstTensor AstMethodLet s' (TKS2 (shm' ++ shn') r)
       -> AstIxS AstMethodLet shm'
       -> AstTensor AstMethodLet s' (TKS2 shn' r)
     astIndexRec _shn' v2 ZIS = v2
     astIndexRec shn' v2 ix2 =
       if knobStepOnly knobs
       then Ast.AstIndexS shn' v2 ix2
       else astIndexKnobsS knobs shn' v2 ix2
     astIndex shn' v2 ix2 =
       if knobStepOnly knobs
       then astIndexKnobsS knobs shn' (astNonIndexStep v2) (simplifyAstIxS ix2)
       else astIndexKnobsS knobs shn' v2 ix2
     astGather
       :: forall shm' shn' shp'.
          ShS shn'
       -> AstTensor AstMethodLet s (TKS2 (shp' ++ shn') r)
       -> (AstVarListS shm', AstIxS AstMethodLet shp')
       -> AstTensor AstMethodLet s (TKS2 (shm' ++ shn') r)
     astGather shn' v2 (vars2, ix2) =
       if knobStepOnly knobs
       then astGatherKnobsS @shm' @shn' @shp'
                            knobs
                            shn' (astNonIndexStep v2)
                            (vars2, simplifyAstIxS ix2)
       else astGatherKnobsS @shm' @shn' @shp' knobs shn' v2 (vars2, ix2)
 in case v0 of
  Ast.AstProject1{} -> Ast.AstIndexS shn v0 ix
  Ast.AstProject2{} -> Ast.AstIndexS shn v0 ix
  Ast.AstFromVector snat stk l | AstConcrete (RepF _ (RepN it)) <- i1
                               , STKS{} <- stk ->
    let i = fromIntegral it
    in if 0 <= i && i < sNatValue snat
       then astIndex shn (l V.! i) rest1
       else let ftk = FTKS shn x
            in fromPrimal $ astConcrete (RepF ftk (constantTarget def ftk))
  Ast.AstFromVector{} | ZIS <- rest1 ->  -- normal form, STKScalar case included
    Ast.AstIndexS shn v0 ix
  Ast.AstFromVector snat stk l | STKS{} <- stk ->
    shareIx rest1 $ \ !ix2 ->
      Ast.AstIndexS @'[in1] @shn shn (astFromVector snat (STKS shn (ftkToSTK x))
                                      $ V.map (\a -> astIndexRec shn a ix2) l)
                    (i1 :.$ ZIS)
  Ast.AstFromVector{} -> error "astIndexKnobsS: impossible case"
  Ast.AstSum snat@(SNat @n1) STKS{} v ->
    let perm3 = backpermCycle $ shsLength (ixsToShS ix) + 1
    in Permutation.permFromList perm3 $ \(perm :: Permutation.Perm perm3P) ->
         gcastWith (unsafeCoerceRefl
                    :: Compare (Rank perm3P) (Rank (n1 : shm ++ shn))
                       :~: LT) $
         gcastWith (unsafeCoerceRefl
                    :: Permutation.PermutePrefix perm3P (n1 : (shm ++ shn))
                       :~: shm ++ (n1 : shn)) $
         trustMeThisIsAPermutation @perm3P $
         astSum snat (STKS shn (ftkToSTK x))
         $ astIndex @shm @(n1 : shn) (snat :$$ shn)
                    (astTransposeS @perm3P @(n1 : shm ++ shn) perm v)
                    ix
  Ast.AstReplicate snat STKS{} v | AstConcrete (RepF _ (RepN it)) <- i1 ->
      let i = fromIntegral it
      in if 0 <= i && i < sNatValue snat
         then astIndex shn v rest1
         else let ftk = FTKS shn x
              in fromPrimal $ astConcrete (RepF ftk (constantTarget def ftk))
{- TODO: this generalization of the above case slows down test 3nestedSumBuild1
   orders of magnitude
  Ast.AstReplicate k v ->
    let len = astConcrete $ fromIntegral k
        zero = astReplicate0N (dropShape $ shapeAst v) 0
    in case simplifyAstBool $ Ast.AstB2 AndOp (Ast.AstRel LeqOp 0 i1)
                                              (Ast.AstRel LsOp i1 len) of
      AstBoolConst b -> if b then astIndex v rest1 else zero
      bExpr -> astCond bExpr (astIndex v rest1) zero -}
  -- TODO: the two below are wrong, should catch out of bounds instead
  Ast.AstReplicate _ STKS{} v -> astIndex shn v rest1
  Ast.AstReplicate _ STKScalar v | ZIS <- rest1 -> astSFromK v
  Ast.AstApply{} -> Ast.AstIndexS shn v0 ix
  Ast.AstVar{} -> Ast.AstIndexS shn v0 ix
  Ast.AstCond b v w ->
    shareIx ix $ \ !ix2 ->
      astCond b (astIndexRec shn v ix2) (astIndexRec shn w ix2)
  Ast.AstBuild1 _snat stk (var2, v) -> case stk of
    STKScalar | ZIS <- rest1 -> astSFromK $ astLet var2 i1 v
    STKS{} -> astIndex shn (astLet var2 i1 v) rest1
  AstConcrete (RepF FTKS{} t) ->
    let unConc :: AstInt AstMethodLet -> Maybe [IntOf RepN]
               -> Maybe [IntOf RepN]
        unConc (AstConcrete (RepF _ i)) (Just l) = Just $ i : l
        unConc _ _ = Nothing
    in case foldr unConc (Just []) ix of
      Just ixInt -> withKnownSTK (ftkToSTK x) $
                    withKnownShS shn $
                    withKnownShS (ixsToShS ix) $
                    withKnownShS (ixsToShS ix `shsAppend` shn) $
                    astConcrete (RepF (FTKS shn x)
                                      (sindex @_ @_ @shm t (fromList ixInt)))
        -- TODO: we'd need mapM for Index to keep this rank-typed
      Nothing -> Ast.AstIndexS shn v0 ix

  Ast.AstLet var u v -> astLet var u (astIndexRec shn v ix)

  Ast.AstPrimalPart{} -> Ast.AstIndexS shn v0 ix  -- must be a NF
  Ast.AstDualPart{} -> Ast.AstIndexS shn v0 ix
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astIndex shn  v ix
  Ast.AstFromDual v -> Ast.AstFromDual $ astIndex shn v ix

  AstSumOfList args ->
    shareIx ix $ \ !ix2 ->
      astSumOfList (NonEmpty.map (\a -> astIndexRec shn a ix2) args)

  AstN1S opCode u -> AstN1S opCode (astIndexRec shn u ix)
  AstN2S opCode u v ->
    shareIx ix $ \ !ix2 ->
    AstN2S opCode (astIndexRec shn u ix2) (astIndexRec shn v ix2)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astIndexRec shn u ix)
  Ast.AstR2S opCode u v ->
    shareIx ix
    $ \ !ix2 -> Ast.AstR2S opCode (astIndexRec shn u ix2)
                                  (astIndexRec shn v ix2)
  Ast.AstI2S opCode u v ->
    shareIx ix
    $ \ !ix2 -> Ast.AstI2S opCode (astIndexRec shn u ix2)
                                  (astIndexRec shn v ix2)
  Ast.AstFloorS v -> Ast.AstFloorS $ astIndexKnobsS knobs shn v ix
  Ast.AstFromIntegralS v -> astFromIntegralS $ astIndexKnobsS knobs shn v ix
  Ast.AstCastS t -> astCastS $ astIndexKnobsS knobs shn t ix

  Ast.AstIndexS _ v (ix2 :: AstIxS AstMethodLet sh4)
    | Refl <- lemAppAssoc (Proxy @sh4) (Proxy @shm) (Proxy @shn) ->
      astIndexS shn v (ix2 `ixsAppend` ix)
  Ast.AstScatterS @shm7 @shn7 @shp7 shn7 v (vars, AstIntVar var5 :.$ ix2)
    | AstIntVar var6 <- i1, var6 == var5 ->
        astIndex shn (astScatterS @shm7 @shn7 @(Tail shp7)
                                  shn7 v (vars, ix2)) rest1
  Ast.AstScatterS @shm7 @shn7 @shp7 shn7
                  v (vars, AstConcrete (RepF _ i5) :.$ ix2)
    | AstConcrete (RepF _ i6) <- i1 ->
        if i6 == i5
        then astIndex shn (astScatterS @shm7 @shn7 @(Tail shp7)
                                       shn7 v (vars, ix2)) rest1
        else let ftk = FTKS shn x
             in fromPrimal $ astConcrete (RepF ftk (tconstantTarget 0 ftk))
  -- AstScatter sh v (vars2, ZIR) ->
  --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZIR)
  Ast.AstScatterS{} ->  -- normal form
    Ast.AstIndexS shn v0 ix
  Ast.AstGatherS @_ @_ @shp' _shn' v (ZS, ix2) ->
    gcastWith (unsafeCoerceRefl
              :: shp' ++ (in1 ': shm1) ++ shn
                 :~: shp' ++ (in1 ': shm1 ++ shn)) $
    astIndex @(shp' ++ shm) @shn shn v (ix2 `ixsAppend` ix)
  Ast.AstGatherS @_ @shn' @shp' shn'
                 v ((::$) @_ @shm71 (Const var2) vars, ix2) ->
    gcastWith (unsafeCoerceRefl :: shm71 ++ shn' :~: shm1 ++ shn) $
      let w :: AstTensor AstMethodLet s (TKS2 (shm1 ++ shn) r)
          w = astGather @shm71 @shn' @shp' shn' v (vars, ix2)
      in astLet var2 i1 $ astIndexS @shm1 @shn shn w rest1
  Ast.AstMinIndexS @n1 @shz v -> case ftkToSTK (ftkAst v) of
    STKS nsh _ -> case shsLast nsh of
     nl@(SNat @nl) ->
      let shnl = shn `shsAppend` (nl :$$ ZSS)
      in gcastWith (unsafeCoerceRefl
                    :: Permutation.Index 0 (shn ++ '[nl])
                       ': Drop 1 (shn ++ '[nl])
                       :~: shn ++ '[nl]) $
         gcastWith (unsafeCoerceRefl
                    :: Init (shn ++ '[nl]) :~: shn) $
         gcastWith (unsafeCoerceRefl
                    :: shm ++ (shn ++ '[nl]) :~: n1 ': shz) $
         Ast.AstMinIndexS @(Head (shn ++ '[nl]))
                          @(Tail (shn ++ '[nl]))
         $ astIndexKnobsS @shm @(shn ++ '[nl]) knobs shnl v ix
  Ast.AstMaxIndexS @n1 @shz v -> case ftkToSTK (ftkAst v) of
    STKS nsh _ -> case shsLast nsh of
     nl@(SNat @nl) ->
      let shnl = shn `shsAppend` (nl :$$ ZSS)
      in gcastWith (unsafeCoerceRefl
                    :: Permutation.Index 0 (shn ++ '[nl])
                       ': Drop 1 (shn ++ '[nl])
                       :~: shn ++ '[nl]) $
         gcastWith (unsafeCoerceRefl
                    :: Init (shn ++ '[nl]) :~: shn) $
         gcastWith (unsafeCoerceRefl
                    :: shm ++ (shn ++ '[nl]) :~: n1 ': shz) $
         Ast.AstMaxIndexS @(Head (shn ++ '[nl]))
                          @(Tail (shn ++ '[nl]))
         $ astIndexKnobsS @shm @(shn ++ '[nl]) knobs shnl v ix
  Ast.AstIotaS{}
    | AstConcrete (RepF _ (RepN i)) <- i1 -> case testEquality shn ZSS of
      Just Refl -> astFromIntegralS
                   $ astConcrete (RepF (FTKS ZSS FTKScalar) (sscalar i))
      _ -> error "astIndexKnobsS: shape not []"
-- TODO:  AstIndexS AstIotaS (i :.$ ZIS) ->
--    sfromIntegral . sfromPrimal . sfromR . rfromK $ interpretAstPrimal env i
  Ast.AstIotaS{} -> Ast.AstIndexS shn v0 ix
  Ast.AstAppendS u v | STKS (SNat @m :$$ _) _ <- ftkToSTK (ftkAst u) ->
    let ulen = AstConcrete (RepF FTKScalar (RepN $ valueOf @m))
        ix1 = i1 :.$ rest1
        ix2 = simplifyAstInt (AstN2K MinusOp i1 ulen) :.$ rest1
    in case simplifyAstBool $ Ast.AstRel LsOp i1 ulen of
      AstBoolConst b -> if b then astIndex shn u ix1 else astIndex shn v ix2
      bExpr -> astCond bExpr (astIndexRec shn u ix1) (astIndexRec shn v ix2)
  Ast.AstSliceS (SNat @i) _ SNat v ->
    let ii = simplifyAstInt (i1 + fromIntegral (valueOf @i :: Int))
      -- we generate this index, so we simplify on the spot
    in astIndex shn v (ii :.$ rest1)
  Ast.AstReverseS v ->
    let iRev = simplifyAstInt (fromIntegral (valueOf @in1 - 1 :: Int) - i1)
      -- we generate this index, so we simplify on the spot
    in astIndex shn v (iRev :.$ rest1)
  Ast.AstTransposeS @perm perm v
    | gcompare (shsRank (ixsToShS ix)) (Permutation.permRank perm) == GLT ->
        astIndex shn (astTransposeAsGatherS @perm knobs perm v) ix
  Ast.AstTransposeS @perm @sh2 perm v ->
    let ix2 :: AstIxS AstMethodLet (Permutation.PermutePrefix perm shm)
        ix2 = ixsPermutePrefix perm ix
    in gcastWith (unsafeCoerceRefl
                  :: sh2 :~: Permutation.PermutePrefix perm shm ++ shn) $
       astIndex @(Permutation.PermutePrefix perm shm) shn v ix2
  Ast.AstReshapeS sh v -> astIndex shn (astReshapeAsGatherS knobs sh v) ix
  Ast.AstZipS _ -> Ast.AstIndexS shn v0 ix
  Ast.AstNestS{} -> Ast.AstIndexS shn v0 ix
  Ast.AstUnNestS _ -> Ast.AstIndexS shn v0 ix

  Ast.AstFromS stkz v -> case sameSTK (ftkToSTK (ftkAst v)) stkz of
    Just Refl -> astIndex shn v ix -- rare, usually simplifies away earlier
    Nothing -> error "astIndexKnobsS: wrong tensor kinds in AstFromS"
  -- These conversions need to stay down, so this is NF, see vectorization.
  Ast.AstSFromR{} -> Ast.AstIndexS shn v0 ix
  Ast.AstSFromX{} -> Ast.AstIndexS shn v0 ix

  -- These should not appear here unless via wacky tests.
  Ast.AstReplicate0NS{} -> Ast.AstIndexS shn v0 ix
-- impossible: Ast.AstSum0S{} -> Ast.AstIndexS shn v0 ix
-- impossible: Ast.AstDot0S{} -> Ast.AstIndexS shn v0 ix
  Ast.AstDot1InS{} -> Ast.AstIndexS shn v0 ix
  Ast.AstMatvecmulS{} -> Ast.AstIndexS shn v0 ix
  Ast.AstMatmul2S{} -> Ast.AstIndexS shn v0 ix

-- TODO: compared to tletIx, it adds many lets, not one, but does not
-- create other (and non-simplified!) big terms and also uses astIsSmall,
-- so it's probably more efficient. Use this instead of tletIx
-- or design something even better.
shareIx :: AstIxS AstMethodLet shm
        -> (AstIxS AstMethodLet shm -> AstTensor AstMethodLet s y)
        -> AstTensor AstMethodLet s y
{-# NOINLINE shareIx #-}
shareIx ix f = unsafePerformIO $ do
  let shareI :: AstInt AstMethodLet
             -> IO ( Maybe (IntVarName, AstInt AstMethodLet)
                   , AstInt AstMethodLet )
      shareI i | astIsSmall True i = return (Nothing, i)
      shareI i = funToAstIntVarIO $ \ (!varFresh, !astVarFresh) ->
                   (Just (varFresh, i), astVarFresh)
  (bindings, ix2) <- mapAndUnzipM shareI (Foldable.toList ix)
  return $! foldr (uncurry Ast.AstLet)
                  (withKnownShS (ixsToShS ix) $ f $ fromList ix2)
                  (catMaybes bindings)

-- TODO: fuse scatters, scatter and sum, perhaps more (fromList?)
astScatterS :: forall shm shn shp r s . AstSpan s
            => ShS shn
            -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
            -> (AstVarListS shm, AstIxS AstMethodLet shp)
            -> AstTensor AstMethodLet s (TKS2 (shp ++ shn) r)
astScatterS _shn v (ZS, ZIS) = v
{- TODO: this is impossible, due to strongly typed index,
-- and checked when indexes are created, right?
astScatterS _v (_vars, (:.$) @k (AstConcrete _ (RepN it)) _ix)
  | let i = fromIntegral it
  , not (0 <= i && i < valueOf @k)
  , STKScalar <- knownSTK @r =
      astReplicate0NS def
-- else update (rzero sh 0) [AstConcreteS it] (astScatter ...) -}
astScatterS shn v (Const var ::$ (vars :: AstVarListS sh3), ix)
  | not $ varNameToAstVarId var `varInIndexS` ix
  , FTKS _ x <- ftkAst v =
      astScatterS @sh3 @shn @shp shn
        (astSum SNat (STKS (listsToShS vars `shsAppend` shn) (ftkToSTK x)) v)
        (vars, ix)
-- astScatterS v (ZR, ix) = update (rzero sh 0) ix v
astScatterS shn (Ast.AstFromPrimal v) (vars, ix) =
  Ast.AstFromPrimal $ astScatterS @shm @shn @shp shn v (vars, ix)
astScatterS shn (Ast.AstFromDual v) (vars, ix) =
  Ast.AstFromDual $ astScatterS @shm @shn @shp shn v (vars, ix)
astScatterS shn v (vars, !ix) = Ast.AstScatterS @shm @shn @shp shn v (vars, ix)

astGatherS
  :: forall shm shn shp r s. AstSpan s
  => ShS shn
  -> AstTensor AstMethodLet s (TKS2 (shp ++ shn) r)
  -> (AstVarListS shm, AstIxS AstMethodLet shp)
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
astGatherS = astGatherKnobsS @shm @shn @shp defaultKnobs

astGatherStepS
  :: forall shm shn shp r s. AstSpan s
  => ShS shn
  -> AstTensor AstMethodLet s (TKS2 (shp ++ shn) r)
  -> (AstVarListS shm, AstIxS AstMethodLet shp)
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
-- TODO: this probably needs an extra condition similar to kN == vkN below
--astGatherStepS v (AstVarName varId ::$ ZSS, AstIntVarS varId2 :.$ ZIS)
--  | varId == varId2 = ...
astGatherStepS shn v (vars, ix) =
  astGatherKnobsS @shm @shn @shp
                  (defaultKnobs {knobStepOnly = True})
                  shn (astNonIndexStep v)
                  (vars, simplifyAstIxS ix)

flipCompare :: forall (a :: Nat) b. Compare a b ~ GT => Compare b a :~: LT
flipCompare = unsafeCoerceRefl

isVar :: AstTensor AstMethodLet s y -> Bool
isVar Ast.AstVar{} = True
isVar (Ast.AstPrimalPart Ast.AstVar{}) = True
isVar (Ast.AstDualPart Ast.AstVar{}) = True
isVar (Ast.AstFromPrimal Ast.AstVar{}) = True
isVar (Ast.AstFromDual Ast.AstVar{}) = True
isVar _ = False

-- Assumption: vars0 don't not occur in v0. The assumption only holds
-- when newly generated variables are fresh, which is the case as long
-- as resetVarCounter is not used. The assumption makes it easier to spot
-- bugs or corruption, hence we assert it in the code below.
--
-- The v0 term is already at least one step simplified,
-- either from full recursive simplification or from astGatherStep.
astGatherKnobsS
  :: forall shm shn shp r s. AstSpan s
  => SimplifyKnobs
  -> ShS shn
  -> AstTensor AstMethodLet s (TKS2 (shp ++ shn) r)
  -> (AstVarListS shm, AstIxS AstMethodLet shp)
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
astGatherKnobsS knobs shn v0 (!vars0, !ix0) | FTKS _ x <- ftkAst v0 =
  case (listsToShS vars0, (vars0, ix0)) of
    _ | any (`varNameInAst` v0) $ listsToList vars0 ->
      error $ "astGatherS: gather vars in v0: "
              ++ show (vars0, v0)
    (_, (ZS, _)) -> astIndex shn v0 ix0
    (_, (_, ZIS)) -> if knobExpand knobs
                     then Ast.AstGatherS shn v0 (vars0, ix0)
                     else astReplicateNS @shm @shn (listsToShS vars0) v0
    (shm@( k :$$ sh'), (var ::$ vars, i1 :.$ rest1)) ->
      if | not (any (`varNameInAst` i1) $ listsToList vars0) ->
           astGatherKnobsS @shm @shn @(Tail shp)
             knobs shn
             (astIndex (ixsToShS rest1 `shsAppend` shn) v0 (i1 :.$ ZIS))
             (vars0, rest1)
         | case iN of
             AstIntVar varN' ->
               varN' == getConst varN
               && not (any (getConst varN `varNameInAst`) restN)
             _ -> False
         , kN@SNat <- shsLast shm
         , vkN@SNat <- shsLast (ixsToShS ix0)
         , case testEquality kN vkN of
             Just Refl -> True
             _ -> False
           -> gcastWith (unsafeCoerceRefl
                         :: Init shp ++ (Last shm ': shn) :~: shp ++ shn) $
              gcastWith (unsafeCoerceRefl
                         :: Init shm ++ (Last shm ': shn) :~: shm ++ shn) $
              astGatherKnobsS @(Init shm) @(Last shm ': shn) @(Init shp)
                              knobs (shsLast (listsToShS vars0) :$$ shn)
                              v0 (varsN, restN)
         | varInIndexS (varNameToAstVarId $ getConst var) ix0 ->
           astGatherCase @shm @shn @shp shn v0 (vars0, ix0)
         | otherwise ->
           if knobExpand knobs
           then Ast.AstGatherS @shm @shn @shp shn v0 (vars0, ix0)
           else astReplicate k (STKS (sh' `shsAppend` shn) (ftkToSTK x))
                             (astGatherKnobsS @(Tail shm) @shn @shp
                                              knobs shn v0 (vars, ix0))
       where
        restN = ixsInit ix0
        iN = ixsLast ix0
        varsN = listsInit vars0
        varN = listsLast vars0
 where
  astIndex
    :: forall shm' shn' s'. AstSpan s'
    => ShS shn' -> AstTensor AstMethodLet s' (TKS2 (shm' ++ shn') r)
    -> AstIxS AstMethodLet shm'
    -> AstTensor AstMethodLet s' (TKS2 shn' r)
  astIndex shn' v2 ix2 =
    if knobStepOnly knobs
    then astIndexKnobsS knobs shn'
                        (astNonIndexStep v2) (simplifyAstIxS ix2)
    else astIndexKnobsS knobs shn' v2 ix2
  astGatherRec, astGather
    :: forall shm' shn' shp' s' r'. AstSpan s'
    => ShS shn'
    -> AstTensor AstMethodLet s' (TKS2 (shp' ++ shn') r')
    -> (AstVarListS shm', AstIxS AstMethodLet shp')
    -> AstTensor AstMethodLet s' (TKS2 (shm' ++ shn') r')
  astGatherRec shn' v2 (!vars2, !ix2) =
    if knobStepOnly knobs
    then Ast.AstGatherS @shm' @shn' @shp' shn' v2 (vars2, ix2)
    else astGatherKnobsS @shm' @shn' @shp' knobs shn' v2 (vars2, ix2)
  astGather shn' v2 (vars2, ix2) =
    if knobStepOnly knobs
    then astGatherKnobsS @shm' @shn' @shp'
                         knobs
                         shn' (astNonIndexStep v2)
                         (vars2, simplifyAstIxS ix2)
    else astGatherKnobsS @shm' @shn' @shp' knobs shn' v2 (vars2, ix2)
  -- Note that v4 is in weak head normal form and so can't one-step reduce
  -- and so we don't have to reduce it to expose any top redexes.
  astGatherCase
    :: forall shm' shn' shp'.
       ShS shn'
    -> AstTensor AstMethodLet s (TKS2 (shp' ++ shn') r)
    -> (AstVarListS shm', AstIxS AstMethodLet shp')
    -> AstTensor AstMethodLet s (TKS2 (shm' ++ shn') r)
  astGatherCase _shn' v4 (vars4, ZIS) =
    astReplicateNS @shm' @shn' (listsToShS vars4) v4  -- not really possible
  astGatherCase shn' v4 ( !vars4
                        , ix4@((:.$) @p1' @shp1' i4 rest4) )
   | FTKS _ x <- ftkAst v4 = case v4 of
    Ast.AstProject1{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstProject2{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstFromVector snat stk l | AstConcrete (RepF _ (RepN it)) <- i4
                                 , STKS{} <- stk ->
      let i = fromIntegral it
      in if 0 <= i && i < sNatValue snat
         then astGather @shm' @shn' @shp1' shn' (l V.! i) (vars4, rest4)
         else let ftk = FTKS (listsToShS vars4 `shsAppend` shn') x
              in fromPrimal $ astConcrete (RepF ftk (constantTarget def ftk))
    Ast.AstFromVector{} | gatherFromNFS (ixsToShS rest4) vars4 ix4 ->
        -- normal form,
        -- STKScalar case included
      Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstFromVector snat stk l | STKS{} <- stk ->
      -- Term rest4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use tlet.
      funToVarsIxS @shm' (listsToShS vars4) $ \ (!varsFresh, IxS !ixFresh) ->
        let f v = astGatherRec @shm' @shn' @shp1' shn' v (vars4, rest4)
            -- This subst doesn't currently break sharing because it's a rename.
            subst i =
              foldr (\(i2, var2) v2 ->
                      substituteAst i2 var2 v2)
                    i
                    (listsToList $ zipSizedS ixFresh vars4)
            i5 = subst i4
       in astGather @shm' @shn' @(p1' ': shm')
                    shn' (astFromVector snat (STKS (listsToShS varsFresh
                                                    `shsAppend` shn')
                                                   (ftkToSTK x))
                          $ V.map f l)
                    (varsFresh, i5 :.$ IxS ixFresh)
    Ast.AstFromVector{} -> error "astGatherCase: impossible case"
    Ast.AstSum snat@(SNat @n1) STKS{} v ->
      let perm3 = backpermCycle $ shsLength (ixsToShS ix4) + 1
          perm4 = permCycle $ shsLength (listsToShS vars4) + 1
      in Permutation.permFromList perm3
         $ \(perm3S :: Permutation.Perm perm3P) ->
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
         let innerGather =
               astGather @shm' @(n1 : shn') @shp'
                         (snat :$$ shn') (astTransposeS perm3S v) (vars4, ix4)
         in astSum snat (STKS (listsToShS vars4 `shsAppend` shn') (ftkToSTK x))
            $ if not (knobExpand knobs)
                 || length perm4 <= shsLength (listsToShS vars4)
              then astTransposeS perm4S innerGather
              else astTransposeAsGatherS knobs perm4S innerGather
    Ast.AstReplicate snat STKS{} v | AstConcrete (RepF _ (RepN it)) <- i4 ->
      let i = fromIntegral it
      in if 0 <= i && i < sNatValue snat
         then astGather @shm' @shn' @shp1' shn' v (vars4, rest4)
         else let ftk = FTKS (listsToShS vars4 `shsAppend` shn') x
              in fromPrimal $ astConcrete (RepF ftk (constantTarget def ftk))
    Ast.AstReplicate _ STKS{} v ->
      astGather @shm' @shn' @shp1' shn' v (vars4, rest4)
    Ast.AstReplicate _ STKScalar v | ZIS <- rest4 ->
      astGather @shm' @shn' @shp1' shn' (astSFromK v) (vars4, rest4)
    Ast.AstApply{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstVar{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstCond b v w ->
      astCond b (astGather @shm' @shn' @shp' shn' v (vars4, ix4))
                (astGather @shm' @shn' @shp' shn' w (vars4, ix4))
    Ast.AstBuild1{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    AstConcrete{} ->  -- free variables possible, so can't compute the tensor
      Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)

    Ast.AstLet var u v ->
      astLet var u (astGatherCase @shm' @shn' @shp' shn' v (vars4, ix4))

    Ast.AstPrimalPart{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstDualPart{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstFromPrimal v ->
      Ast.AstFromPrimal $ astGather @shm' @shn' @shp' shn' v (vars4, ix4)
    Ast.AstFromDual v ->
      Ast.AstFromDual $ astGather @shm' @shn' @shp' shn' v (vars4, ix4)

    AstSumOfList{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)

    AstN1S opCode v | not (isVar v) ->
      AstN1S opCode (astGatherRec @shm' @shn' @shp' shn' v (vars4, ix4))
    AstN1S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    AstN2S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
      -- Going inside AstN2R usually makes the term more expensive to interpret
      -- and reverting this transformation requires comparing two arguments,
      -- so it's not practical.
    Ast.AstR1S opCode v | not (isVar v) ->
      Ast.AstR1S opCode (astGatherRec @shm' @shn' @shp' shn' v (vars4, ix4))
    Ast.AstR1S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstR2S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstI2S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstFloorS v ->
      Ast.AstFloorS
      $ astGatherKnobsS @shm' @shn' @shp' knobs shn' v (vars4, ix4)
    Ast.AstFromIntegralS v ->
      astFromIntegralS $ astGather @shm' @shn' @shp' shn' v (vars4, ix4)
    Ast.AstCastS v -> astCastS $ astGather @shm' @shn' @shp' shn' v (vars4, ix4)

    Ast.AstIndexS @shm2 _shn2 v2 ix2 -> case (v2, ix2) of
      (Ast.AstFromVector{}, i2 :.$ ZIS) ->
        astGather @shm' @shn' @(shm2 ++ shp') shn' v2 (vars4, i2 :.$ ix4)
      _ ->  -- AstVar, AstConcrete
        Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstScatterS @shm7 @shn7 @shp7 shn7 v (vars, AstIntVar var5 :.$ ix2)
      | AstIntVar var6 <- i4, var6 == var5 ->
          astGather @shm' @shn' @shp1' shn'
                    (astScatterS @shm7 @shn7 @(Tail shp7) shn7
                                 v (vars, ix2))
                    (vars4, rest4)
    Ast.AstScatterS shn7 v (vars, AstConcrete (RepF _ i5) :.$ ix2)
      | AstConcrete (RepF _ i6) <- i4 ->
          if i6 == i5
          then astGather @shm' @shn' @shp1' shn'
                         (astScatterS shn7 v (vars, ix2))
                         (vars4, rest4)
          else let ftk = FTKS (listsToShS vars4 `shsAppend` shn') x
               in fromPrimal $ astConcrete (RepF ftk (tconstantTarget def ftk))
                    -- TODO: or 0? review again and comment
    Ast.AstScatterS{} ->  -- normal form
      Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstGatherS @shm2 @shn2 @shp2 shn2 v2 (vars2, ix2)
                   | SNat @rank4 <- ixsRank ix4
                   , SNat @rank2 <- listsRank vars2 ->
      -- Term ix4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use tlet.
      --
      -- Independently, we need to insert lets to each index element,
      -- bloating the term. TODO: would going via a rank 1 vector,
      -- as in tletIx help or would we need to switch indexes to vector
      -- altogether (terrible for user comfort, especially wrt typing).
      let substLet :: AstIxS AstMethodLet shm7 -> AstVarListS shm7
                   -> AstInt AstMethodLet
                   -> AstInt AstMethodLet
          substLet (IxS ix) vars i =
            simplifyAstInt  -- we generate the index, so we simplify on the spot
            $ foldr (uncurry astLetInt) i
                    (listsToList $ zipSizedS vars ix)
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
            in astGather shn2 v2 (list422, ix22)
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
            in astGather shn' v2 (vars4, ix2244)
      in case cmpNat (Proxy @rank4) (Proxy @rank2) of
        LTI -> composedGather
        EQI -> assimilatedGather
        GTI -> gcastWith (flipCompare @rank4 @rank2) assimilatedGather
    Ast.AstMinIndexS @n @sh v -> case ftkToSTK (ftkAst v) of
     STKS nsh _ -> case shsLast nsh of
      nl@(SNat @nl) ->
        let shnl = shn' `shsAppend` (nl :$$ ZSS)
        in gcastWith (unsafeCoerceRefl
                     :: shp' ++ (shn' ++ '[nl]) :~: n ': sh) $
           gcastWith (unsafeCoerceRefl
                      :: Head (shm' ++ (shn' ++ '[nl]))
                         ': (Tail (shm' ++ (shn' ++ '[nl])))
                         :~: shm' ++ (shn' ++ '[nl])) $
           gcastWith (unsafeCoerceRefl
                      :: Init (shm' ++ (shn' ++ '[nl]))
                      :~: shm' ++ shn') $
           Ast.AstMinIndexS @(Head (shm' ++ (shn' ++ '[nl])))
                            @(Tail (shm' ++ (shn' ++ '[nl])))
           $ astGatherKnobsS knobs shnl v (vars4, ix4)
    Ast.AstMaxIndexS @n @sh v -> case ftkToSTK (ftkAst v) of
     STKS nsh _ -> case shsLast nsh of
      nl@(SNat @nl) ->
        let shnl = shn' `shsAppend` (nl :$$ ZSS)
        in gcastWith (unsafeCoerceRefl
                     :: shp' ++ (shn' ++ '[nl]) :~: n ': sh) $
           gcastWith (unsafeCoerceRefl
                      :: Head (shm' ++ (shn' ++ '[nl]))
                         ': (Tail (shm' ++ (shn' ++ '[nl])))
                         :~: shm' ++ (shn' ++ '[nl])) $
           gcastWith (unsafeCoerceRefl
                      :: Init (shm' ++ (shn' ++ '[nl]))
                      :~: shm' ++ shn') $
           Ast.AstMaxIndexS @(Head (shm' ++ (shn' ++ '[nl])))
                            @(Tail (shm' ++ (shn' ++ '[nl])))
           $ astGatherKnobsS knobs shnl v (vars4, ix4)
    Ast.AstIotaS{} | AstConcrete (RepF _ (RepN i)) <- i4 ->
      astFromIntegralS
      $ let ftk = FTKS (listsToShS vars4 `shsAppend` shn') (FTKScalar @Int64)
        in fromPrimal
           $ astConcrete (RepF ftk (constantTarget (fromIntegral i) ftk))
    Ast.AstIotaS{} ->  -- probably nothing can be simplified; a normal form
      Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstAppendS u v | STKS (SNat @m :$$ _) _ <- ftkToSTK (ftkAst u) ->
      let ulen = AstConcrete (RepF FTKScalar (RepN $ valueOf @m))
          iu = simplifyAstInt (AstN2K MinusOp i4 ulen)
      in case simplifyAstBool $ Ast.AstRel LsOp i4 ulen of
        AstBoolConst b -> if b
                          then astGather shn' u (vars4, i4 :.$ rest4)
                          else astGather shn' v (vars4, iu :.$ rest4)
        bExpr ->
          funToVarsIxS @shm' (listsToShS vars4)
          $ \ (!varsFresh, IxS !ixFresh) ->
            let u2 = astGatherRec shn' u (vars4, i4 :.$ rest4)
                v2 = astGatherRec shn' v (vars4, iu :.$ rest4)
                -- This subst doesn't break sharing because it's a rename.
                subst i =
                  foldr (uncurry substituteAstBool) i
                        (listsToList $ zipSizedS ixFresh vars4)
                bExpr5 = subst bExpr
            in astGather
                 shn' (astFromVector
                         (SNat @2) (STKS (listsToShS vars4
                                          `shsAppend` shn')
                                         (ftkToSTK x))
                       $ V.fromList [u2, v2])
                 (varsFresh, astCond bExpr5 0 1 :.$ IxS ixFresh)
    Ast.AstSliceS i@SNat _ SNat v ->
      let ii = simplifyAstInt (i4 + fromIntegral (sNatValue i))
        -- we generate this index, so we simplify on the spot
      in astGather shn' v (vars4, ii :.$ rest4)
    Ast.AstReverseS @n v ->
      let iRev = simplifyAstInt ((valueOf @n - 1) - i4)
        -- we generate this index, so we simplify on the spot
      in astGather @shm' @shn' shn' v (vars4, iRev :.$ rest4)
    Ast.AstTransposeS @perm @sh perm v | STKS sh _ <- ftkToSTK (ftkAst v) ->
      let rankPerm = Permutation.permRank perm
      in case gcompare (ixsRank ix4) rankPerm of
        GLT ->  -- TODO: this does not provide any proof, so use cmpNat :(
          if knobExpand knobs
          then astGather @shm' @shn' @shp'
                         shn' (astTransposeAsGatherS knobs perm v) (vars4, ix4)
          else Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
        _ ->
          gcastWith (lemRankMapJust $ shsTakeLen perm sh) $
          gcastWith (unsafeCoerceRefl :: Rank (TakeLen perm sh) :~: Rank perm) $
          permInverse perm
          $ \ (invperm :: Nested.Perm invperm) proof ->
            case proof (ssxFromShape $ shCvtSX $ shsTakeLen perm sh) of
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
                in astGather shn' v (vars4, invix4)
    Ast.AstReshapeS sh v ->
      if knobExpand knobs
      then astGather @shm' @shn' @shp' shn'
                     (astReshapeAsGatherS knobs sh v) (vars4, ix4)
      else Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstZipS _v -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstNestS{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstUnNestS _v -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)

    Ast.AstFromS stkz v -> case sameSTK (ftkToSTK (ftkAst v)) stkz of
      Just Refl -> astGatherCase @shm' @shn' @shp' shn' v (vars4, ix4)
        -- rare, usually simplifies away earlier
      Nothing -> error "astGatherCase: wrong tensor kinds in AstFromS"
    -- These conversions need to stay down.
    Ast.AstSFromR{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstSFromX{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)

    -- These should not appear here unless via wacky tests.
    Ast.AstReplicate0NS{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
--    Ast.AstSum0S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
--    Ast.AstDot0S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstDot1InS{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstMatvecmulS{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstMatmul2S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)

gatherFromNFS :: forall shm n shp.
                 ShS shp -> AstVarListS shm
                 -> AstIxS AstMethodLet (n ': shp) -> Bool
gatherFromNFS shp vars (i :.$ IxS rest) | SNat <- shsRank shp =
  case gcompare (listsRank rest) (listsRank vars) of
    GGT -> False  -- this does not provide any proof, but it's fine
    _ ->
      withKnownShS (listsToShS vars) $
      withKnownShS (takeShS @(Rank shp) $ listsToShS vars) $
      withKnownShS (dropShS @(Rank shp) $ listsToShS vars) $
      let cmp (AstIntVar var1, AstIntVar var2) = var1 == var2
          cmp _ = False
          (varsP, varsPM) = splitAt_Sized @_ @(Rank shp) vars
          --TODO: varsP = listsTakeLen rest vars
          --varsPM = listsDropLen rest vars
          --varsP = takeShS @(Rank shp) vars
          --varsPM = dropShS @(Rank shp) vars
          intVars = listsFmap (Const . AstIntVar . getConst) varsP
      in case testEquality (takeShS @(Rank shp) (listsToShS vars)) shp of
           Just Refl -> all cmp (toList $ zipSizedS rest intVars)
                        && not (any (`varNameInAst` i) $ toList varsPM)
           Nothing -> False

astAppendS :: AstSpan s
           => AstTensor AstMethodLet s (TKS2 (m ': sh) r)
           -> AstTensor AstMethodLet s (TKS2 (n ': sh) r)
           -> AstTensor AstMethodLet s (TKS2 ((m + n) ': sh) r)
astAppendS (Ast.AstFromVector (SNat @k1) stk2 l1)
           (Ast.AstFromVector (SNat @k2) stk3 l2) | STKS{} <- stk2
                                                  , STKS{} <- stk3 =
  astFromVector (SNat @(k1 + k2)) stk2 $ l1 V.++ l2
astAppendS (AstConcrete (RepF (FTKS (SNat :$$ sh) x) u))
           (AstConcrete (RepF (FTKS (SNat :$$ _) _) v)) =
  withKnownSTK (ftkToSTK x) $
  withKnownShS sh $
  astConcrete (RepF (FTKS (SNat :$$ sh) x) (sappend u v))
astAppendS (Ast.AstFromPrimal u) (Ast.AstFromPrimal v) =
  Ast.AstFromPrimal $ astAppendS u v
astAppendS (Ast.AstFromDual u) (Ast.AstFromDual v) =
  Ast.AstFromDual $ astAppendS u v
astAppendS u v = Ast.AstAppendS u v

astSliceS :: forall i n k sh s r. AstSpan s
          => SNat i -> SNat n -> SNat k
          -> AstTensor AstMethodLet s (TKS2 (i + n + k ': sh) r)
          -> AstTensor AstMethodLet s (TKS2 (n ': sh) r)
astSliceS SNat SNat SNat (Ast.AstFromVector _ stk l) | STKS{} <- stk =
  astFromVector (SNat @n) stk $ V.take (valueOf @n) $ V.drop (valueOf @i) l
astSliceS SNat SNat SNat (Ast.AstReplicate _ snat@STKS{} v) =
  astReplicate (SNat @n) snat v
astSliceS SNat SNat SNat (AstConcrete (RepF (FTKS (_ :$$ sh) x) t)) =
  withKnownSTK (ftkToSTK x) $
  withKnownShS sh $
  astConcrete (RepF (FTKS (SNat @n :$$ sh) x) (sslice (Proxy @i) (Proxy @n) t))
astSliceS i n k (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astSliceS i n k v
astSliceS i n k (Ast.AstFromDual v) = Ast.AstFromDual $ astSliceS i n k v
astSliceS SNat SNat SNat v | Just Refl <- sameNat (Proxy @i) (Proxy @0)
                           , Just Refl <- sameNat (Proxy @k) (Proxy @0) = v
astSliceS SNat SNat SNat (Ast.AstGatherS shn v (Const var ::$ vars, ix)) =
  let ivar = AstIntVar var + valueOf @i
      ix2 = substituteAstIxS ivar var ix  -- cheap subst, because ivar is tiny
      vars2 = Const var ::$ vars
  in astGatherS shn v (vars2, ix2)
astSliceS i@SNat n@SNat k@SNat
          w@(Ast.AstAppendS
               (u :: AstTensor AstMethodLet s (TKS2 (ulen : sh) r))
               (v :: AstTensor AstMethodLet s (TKS2 (vlen : sh) r)))
 | STKS (SNat :$$ _) _ <- ftkToSTK (ftkAst u) =
  case cmpNat (Proxy @(i + n)) (Proxy @ulen) of
    LTI -> astSliceS i n (SNat @(ulen - (i + n))) u
    EQI -> astSliceS i n (SNat @0) u
    GTI ->
      gcastWith (unsafeCoerceRefl :: vlen :~: i - ulen + n + k) $
      case cmpNat (Proxy @ulen) (Proxy @i) of
        LTI -> astSliceS (SNat @(i - ulen)) n k v
        EQI -> astSliceS (SNat @0) n k v
        GTI -> Ast.AstSliceS i n k w -- cheap iff fits in one
astSliceS i n k v = Ast.AstSliceS i n k v
{- TODO: is this beneficial? for i==0 and for i/=0?
  AstSliceS @i @n AstIotaS ->
    let i = valueOf @i
        n = valueOf @n
    in interpretAst env
       $ AstConcrete (FTKS knownShS FTKScalar)
       $ RepN $ Nested.sfromListPrimLinear Nested.knownShS
       $ map fromIntegral [i :: Int .. i + n - 1]
-}

astReverseS :: forall n sh s r. AstSpan s
            => AstTensor AstMethodLet s (TKS2 (n ': sh) r)
            -> AstTensor AstMethodLet s (TKS2 (n ': sh) r)
astReverseS (Ast.AstFromVector snat stk l) =
  astFromVector snat stk $ V.reverse l
astReverseS (Ast.AstReplicate snat stk v) = astReplicate snat stk v
astReverseS (AstConcrete (RepF ftk@(FTKS (SNat :$$ sh) x) t)) =
  withKnownSTK (ftkToSTK x) $
  withKnownShS sh $
  astConcrete (RepF ftk (sreverse t))
astReverseS (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astReverseS v
astReverseS (Ast.AstFromDual v) = Ast.AstFromDual $ astReverseS v
astReverseS (Ast.AstGatherS @shm @shn @shp
                            shn v ((::$) @k (Const var) vars, ix)) =
  let ivar = valueOf @k - AstIntVar var
      ix2 = substituteAstIxS  -- cheap subst, because ivar is tiny
              ivar var ix
  in astGatherS @shm @shn @shp shn v (Const var ::$ vars, ix2)
astReverseS (Ast.AstReverseS v) = v
astReverseS v = Ast.AstReverseS v

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astTransposeAsGather needs to be called in addition
-- if full simplification is required.
astTransposeS :: forall perm sh s r.
                 (PermC perm, Rank perm <= Rank sh, AstSpan s)
              => Permutation.Perm perm -> AstTensor AstMethodLet s (TKS2 sh r)
              -> AstTensor
                   AstMethodLet s (TKS2 (Permutation.PermutePrefix perm sh) r)
astTransposeS perm t = case perm of
 Permutation.PNil -> t
 _ -> case t of
  Ast.AstSum snat@(SNat @n) (STKS sh x) v ->
    let zsuccP :: Permutation.Perm (0 : Permutation.MapSucc perm)
        zsuccP = Permutation.permShift1 perm
    in
      gcastWith (unsafeCoerceRefl :: Rank (0 : Permutation.MapSucc perm)
                                     :~: 1 + Rank perm) $
      gcastWith (unsafeCoerceRefl
                 :: Permutation.PermutePrefix (0 : Permutation.MapSucc perm) (n : sh)
                    :~: n : Permutation.PermutePrefix perm sh) $
      trustMeThisIsAPermutation @(0 : Permutation.MapSucc perm) $
      astSum snat (STKS (shsPermutePrefix perm sh) x) $ astTransposeS zsuccP v
  AstConcrete (RepF (FTKS sh x) v) ->
    let shPerm = Nested.Internal.Shape.shsPermutePrefix perm sh
    in withKnownShS sh $
       withKnownSTK (ftkToSTK x) $
       astConcrete (RepF (FTKS shPerm x) (stranspose perm v))

  Ast.AstLet var u v ->
    astLet var u (astTransposeS perm v)

  Ast.AstFromPrimal v ->
    Ast.AstFromPrimal $ astTransposeS perm v
  Ast.AstFromDual v ->
    Ast.AstFromDual $ astTransposeS perm v

  AstN1S opCode u | not (isVar u) ->
    AstN1S opCode (astTransposeS perm u)
  AstN2S opCode u v | not (isVar u && isVar v) ->
    AstN2S opCode (astTransposeS perm u) (astTransposeS perm v)
  Ast.AstR1S opCode u | not (isVar u) ->
    Ast.AstR1S opCode (astTransposeS perm u)
  Ast.AstR2S opCode u v | not (isVar u && isVar v) ->
    Ast.AstR2S opCode (astTransposeS perm u) (astTransposeS perm v)

  Ast.AstScatterS @shm @shn @shp shn v (vars, ix)
    -- TODO: should the below be backpermute or permute?
    | gcompare (Permutation.permRank perm) (ixsRank ix) /= GGT ->
        let ix2 :: AstIxS AstMethodLet (Permutation.PermutePrefix perm shp)
            ix2 = ixsPermutePrefix perm ix
        in gcastWith (unsafeCoerceRefl
                      :: Permutation.PermutePrefix perm shp ++ shn
                         :~: Permutation.PermutePrefix perm (shp ++ shn)) $
           astScatterS @shm @shn @(Permutation.PermutePrefix perm shp)
                       shn v (vars, ix2)
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix)
    -- TODO: should the below be backpermute or permute?
    | gcompare (Permutation.permRank perm) (listsRank vars) /= GGT ->
        let vars2 :: AstVarListS (Permutation.PermutePrefix perm shm)
            vars2 = Nested.Internal.Shape.listsPermutePrefix perm vars
        in gcastWith (unsafeCoerceRefl
                      :: Permutation.PermutePrefix perm shm ++ shn
                         :~: Permutation.PermutePrefix perm (shm ++ shn)) $
           astGatherS @(Permutation.PermutePrefix perm shm) @shn @shp
                      shn v (vars2, ix)
  Ast.AstTransposeS @_ @sh2 perm2 u | STKS sh2 _ <- ftkToSTK (ftkAst u) ->
    -- TODO: try to perform at type level
    let permV = Permutation.permToList' perm
        perm2V = Permutation.permToList' perm2
        perm2Matched =
          perm2V
          ++ take (length permV - length perm2V) (drop (length perm2V) [0 ..])
        perm3V = normalizePermutationHack
                 $ backpermutePrefixList permV perm2Matched
    in Permutation.permFromList perm3V $ \(perm3 :: Permutation.Perm perm3) ->
      trustMeThisIsAPermutation @perm3 $
      gcastWith (unsafeCoerceRefl
                 :: Permutation.PermutePrefix perm3 sh2
                    :~: Permutation.PermutePrefix perm sh) $
      case compare (length perm3V) (Nested.Internal.Shape.shsLength sh2) of
        LT -> gcastWith (unsafeCoerceRefl
                         :: Compare (Rank perm3) (Rank sh2) :~: LT) $
              astTransposeS perm3 u
        EQ -> gcastWith (unsafeCoerceRefl
                         :: Compare (Rank perm3) (Rank sh2) :~: EQ) $
              astTransposeS perm3 u
        GT -> error "astTransposeS: GT"
  u -> Ast.AstTransposeS @perm perm u  -- TODO

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astReshapeAsGather needs to be called in addition
-- if full simplification is required.
astReshapeS :: forall sh sh2 x s. (Product sh ~ Product sh2, AstSpan s)
            => ShS sh2 -> AstTensor AstMethodLet s (TKS2 sh x)
            -> AstTensor AstMethodLet s (TKS2 sh2 x)
astReshapeS sh2 = \case
  Ast.AstFromVector snat stk l
    | Just Refl <- testEquality snat (SNat @1)
    , STKS{} <- stk ->
      astReshapeS sh2 (l V.! 0)
  Ast.AstReplicate (SNat @k) (STKS _ _) x
    | Just Refl <- sameNat (Proxy @k) (Proxy @1) ->
      astReshapeS sh2 x
  AstConcrete (RepF (FTKS sh x) t) ->
    withKnownShS sh $
    withKnownShS sh2 $
    withKnownSTK (ftkToSTK x) $
    astConcrete (RepF (FTKS sh2 x) (sreshape t))
  Ast.AstLet var u v -> astLet var u (astReshapeS @_ @sh2 sh2 v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astReshapeS sh2 v
  Ast.AstFromDual v -> Ast.AstFromDual $ astReshapeS sh2 v
  AstN1S opCode u | not (isVar u) -> AstN1S opCode (astReshapeS @_ @sh2 sh2 u)
  AstN2S opCode u v | not (isVar u && isVar v) ->
    AstN2S opCode (astReshapeS @_ @sh2 sh2 u) (astReshapeS @_ @sh2 sh2 v)
  Ast.AstR1S opCode u | not (isVar u) ->
    Ast.AstR1S opCode (astReshapeS @_ @sh2 sh2 u)
  Ast.AstR2S opCode u v | not (isVar u && isVar v) ->
    Ast.AstR2S opCode (astReshapeS @_ @sh2 sh2 u) (astReshapeS @_ @sh2 sh2 v)
  Ast.AstReshapeS _ v -> astReshapeS @_ @sh2 sh2 v
  v | STKS sh _ <- ftkToSTK (ftkAst v) -> case testEquality sh sh2 of
    Just Refl -> v
    _ -> Ast.AstReshapeS sh2 v

astNestS
  :: forall sh1 sh2 x ms s. AstSpan s
  => ShS sh1 -> ShS sh2
  -> AstTensor ms s (TKS2 (sh1 ++ sh2) x)
  -> AstTensor ms s (TKS2 sh1 (TKS2 sh2 x))
astNestS sh1 sh2 t = case t of
  Ast.AstCond b v1 v2 ->
    Ast.AstCond b (astNestS sh1 sh2 v1) (astNestS sh1 sh2 v2)  -- TODO: ??
  Ast.AstLet var u2 d2 ->  -- TODO: good idea?
    astLet var u2 (astNestS sh1 sh2 d2)
  Ast.AstFromPrimal u ->
    Ast.AstFromPrimal $ astNestS sh1 sh2 u
  Ast.AstFromDual u ->
    Ast.AstFromDual $ astNestS sh1 sh2 u
  _ -> Ast.AstNestS sh1 sh2 t

astUnNestS
  :: forall sh1 sh2 x ms s. AstSpan s
  => AstTensor ms s (TKS2 sh1 (TKS2 sh2 x))
  -> AstTensor ms s (TKS2 (sh1 ++ sh2) x)
astUnNestS t = case t of
  Ast.AstCond b v1 v2 ->
    Ast.AstCond b (astUnNestS v1) (astUnNestS v2)  -- TODO: ??
  Ast.AstLet var u2 d2 ->  -- TODO: good idea?
    astLet var u2 (astUnNestS d2)
  Ast.AstFromPrimal u ->
    Ast.AstFromPrimal $ astUnNestS u
  Ast.AstFromDual u ->
    Ast.AstFromDual $ astUnNestS u
--  Ast.AstNestS u -> u
  _ -> Ast.AstUnNestS t

astFromS :: forall y z s.
            STensorKind z -> AstTensor AstMethodLet s y
         -> AstTensor AstMethodLet s z
astFromS stkz v | Just Refl <- sameSTK (ftkToSTK (ftkAst v)) stkz = v
astFromS stkz (Ast.AstFromPrimal v) =
  Ast.AstFromPrimal $ astFromS stkz v
  -- the only case where we don't push up but down so that conversions
  -- don't end up interspersed with AstFromPrimal
astFromS stkz (Ast.AstFromDual v) =
  Ast.AstFromDual $ astFromS stkz v
astFromS stkz (Ast.AstSFromK v)
         | Just Refl <- sameSTK (ftkToSTK (ftkAst v)) stkz = v
astFromS stkz (Ast.AstFromS _ v) = astFromS stkz v
astFromS stkz (Ast.AstSFromR _ v)
         | Just Refl <- sameSTK (ftkToSTK (ftkAst v)) stkz = v
astFromS stkz (Ast.AstSFromX _ v)
         | Just Refl <- sameSTK (ftkToSTK (ftkAst v)) stkz = v
astFromS stkz v = Ast.AstFromS stkz v

-- Compare with tfromS.
astSFrom :: forall y z s. AstSpan s
         => STensorKind z -> AstTensor AstMethodLet s y
         -> AstTensor AstMethodLet s z
astSFrom stkz (Ast.AstFromS _ v)  -- shortcut
         | Just Refl <- sameSTK (ftkToSTK (ftkAst v)) stkz = v
astSFrom stkz v = case (stkz, ftkToSTK (ftkAst v)) of
  (_, stky) | Just Refl <- sameSTK stky stkz -> v
  (STKS ZSS (STKScalar @rz), STKScalar @ry) ->
    case testEquality (typeRep @ry) (typeRep @rz) of
      Just Refl -> astSFromK v
      Nothing -> error "astSFrom: tensor kinds don't match"
  (STKS shz zx, STKR yn@SNat yx) ->
    case (sameSTK yx zx, testEquality (shsRank shz) yn) of
      (Just Refl, Just Refl) -> astSFromR shz v
      _ -> error "astSFrom: tensor kinds don't match"
  (STKS shz zx, STKX shy yx) ->
    case (sameSTK yx zx, testEquality (shsRank shz) (ssxRank shy)) of
      (Just Refl, Just Refl) -> astSFromX shz v
      _ -> error "astSFrom: tensor kinds don't match"
  (STKProduct stkz1 stkz2, STKProduct{})->
    -- TODO: this is bad, we are introducing let with a non-shaped variable
    astLetFun v $ \ !u3 ->
      astPair (astSFrom stkz1 (astProject1 u3))
              (astSFrom stkz2 (astProject2 u3))
  (_, stky) -> error $ "astSFrom: wrong tensor kinds: " ++ show (stky, stkz, v)

astSFromK :: forall r s. (GoodScalar r, AstSpan s)
              => AstTensor AstMethodLet s (TKScalar r)
              -> AstTensor AstMethodLet s (TKS '[] r)
astSFromK t = case t of
  Ast.AstCond b a2 a3 -> Ast.AstCond b (astSFromK a2) (astSFromK a3)
  AstConcrete (RepF FTKScalar (RepN v)) ->
    astConcrete (RepF (FTKS ZSS FTKScalar) (sscalar v))
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astSFromK v
  Ast.AstFromDual v -> Ast.AstFromDual $ astSFromK v
  AstSumOfList args -> astSumOfList $ NonEmpty.map astSFromK args
  AstN1K opCode u -> AstN1S opCode (astSFromK u)
  AstN2K opCode u v -> AstN2S opCode (astSFromK u) (astSFromK v)
-- TODO:  Ast.AstR1K opCode u -> Ast.AstR1S opCode (astSFromK u)
-- TODO:  Ast.AstR2K opCode u v -> Ast.AstR2S opCode (astSFromK u) (astSFromK v)
  Ast.AstI2K opCode u v | Just Refl <- isTensorInt t ->
    Ast.AstI2S opCode (astSFromK u) (astSFromK v)
  Ast.AstFromS _ v ->
    case matchingFTK (ftkAst v) (FTKS ZSS (FTKScalar @r)) of
      Just Refl -> v
      _ -> error $ "astSFromK: unexpected tensor kinds"
  _ -> Ast.AstSFromK t

-- We are pushing conversions to shaped tensors down, into concrete values
-- and towards variables, which we convert from shaped to ranked and mixed
-- so that the conversions cancel out. Consequently, the conversions away
-- from shaped are pushed up.
astSFromR :: forall sh s r. AstSpan s
          => ShS sh -> AstTensor AstMethodLet s (TKR2 (Rank sh) r)
          -> AstTensor AstMethodLet s (TKS2 sh r)
astSFromR sh a0 = case a0 of
  Ast.AstProject1{} -> Ast.AstSFromR sh a0  -- TODO: convert arbitrary tensor?
  Ast.AstProject2{} -> Ast.AstSFromR sh a0
  Ast.AstFromVector snat@SNat stk l
   | STKR _ x <- stk -> case sh of
     snat2 :$$ rest | Just Refl <- sameNat snat snat2 ->
       astFromVector snat (STKS rest x) (V.map (astSFromR rest) l)
     _ -> error "astSFromR: impossible shape"
  Ast.AstSum snat@SNat (STKR _ x) a ->
    astSum snat (STKS sh x) (astSFromR (snat :$$ sh) a)
  Ast.AstReplicate snat@SNat (STKR SNat x) a -> case sh of
    snat2 :$$ rest | Just Refl <- sameNat snat snat2 ->
      astReplicate snat (STKS rest x) (astSFromR rest a)
    _ -> error "astSFromR: impossible shape"
  Ast.AstApply{} -> Ast.AstSFromR sh a0
  Ast.AstVar{} -> Ast.AstSFromR sh a0
  Ast.AstCond b v w -> astCond b (astSFromR sh v) (astSFromR sh w)
  Ast.AstBuild1 snat@(SNat @k) _ (var, v) -> case ftkAst v of
    FTKR sh' x ->
      withCastRS sh' $ \(sh2 :: ShS sh2) ->
        gcastWith (unsafeCoerceRefl :: k ': sh2 :~: sh) $
        let !v2 = astSFromR sh2 v
        in Ast.AstBuild1 snat (STKS sh2 (ftkToSTK x)) (var, v2)
  AstConcrete (RepF (FTKR _ x) v) | SNat <- shsRank sh ->
    withKnownShS sh $
    withKnownSTK (ftkToSTK x) $
    astConcrete (RepF (FTKS sh x) (sfromR v))

  Ast.AstLet var u v -> astLet var u (astSFromR sh v)

  Ast.AstPrimalPart a -> astPrimalPart $ astSFromR sh a
  Ast.AstDualPart a -> astDualPart $ astSFromR sh a
  Ast.AstFromPrimal a -> Ast.AstFromPrimal $ astSFromR sh a
  Ast.AstFromDual a -> Ast.AstFromDual $ astSFromR sh a

  AstSumOfList args -> astSumOfList (NonEmpty.map (astSFromR sh) args)

  Ast.AstFromS _ v | FTKR _ x <- ftkAst a0 ->
    case matchingFTK (FTKS sh x) (ftkAst v) of
      Just Refl -> v
      _ -> error $ "astSFromR: different tensor kinds in AstSFromR(AstFromS): "
                   ++ show (ftkAst v) ++ " vs "
                   ++ show (FTKS sh x)

-- TODO
astSFromX :: forall sh sh' s r. Rank sh ~ Rank sh'
          => ShS sh -> AstTensor AstMethodLet s (TKX2 sh' r)
          -> AstTensor AstMethodLet s (TKS2 sh r)
astSFromX sh (AstConcrete (RepF ftk t)) = case ftk of
  FTKX sh' x ->
    withKnownSTK (ftkToSTK x) $
    withKnownShS sh $
    withKnownShX (ssxFromShape sh') $
    astConcrete (RepF (FTKS sh x) (sfromX t))
astSFromX sh (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astSFromX sh v
astSFromX sh (Ast.AstFromDual v) = Ast.AstFromDual $ astSFromX sh v
astSFromX sh w@(Ast.AstFromS _ v) | FTKX _ x <- ftkAst w =
  case matchingFTK (FTKS sh x) (ftkAst v) of
    Just Refl -> v
    _ -> error "astSFromX: different shapes in AstSFromX(AstFromS)"
astSFromX sh v = Ast.AstSFromX sh v


-- * Helper combinators

astLetFun :: forall y z s s2. (AstSpan s, AstSpan s2)
          => AstTensor AstMethodLet s y
          -> (AstTensor AstMethodLet s y -> AstTensor AstMethodLet s2 z)
          -> AstTensor AstMethodLet s2 z
astLetFun a f | astIsSmall True a = f a  -- TODO: since astLetFun is now called recursively a lot, ensure astIsSmall is constant, at least except for a constant number of the recursive calls
astLetFun a f = case a of
  Ast.AstFromS @y2 stkz v ->
    let (var, ast) = funToAst (ftkAst v) (f . astFromS @y2 stkz)
    in astLet var v ast
  _ -> case ftkAst a of
    ftk@(FTKR @_ @x sh' x) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        let (var, ast) =
              funToAst (FTKS sh x) (f . astFromS @(TKS2 sh x) (ftkToSTK ftk))
        in astLet var (astSFromR sh a) ast
             -- safe, because subsitution ruled out above
    ftk@(FTKX @_ @x sh' x) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        let (var, ast) =
              funToAst (FTKS sh x) (f . astFromS @(TKS2 sh x) (ftkToSTK ftk))
        in astLet var (astSFromX sh a) ast
    -- TODO: also recursively product, though may be not worth it
    ftk -> let (var, ast) = funToAst ftk f
           in astLet var a ast

astReplicateNS :: forall shn shp s x. AstSpan s
               => ShS shn -> AstTensor AstMethodLet s (TKS2 shp x)
               -> AstTensor AstMethodLet s (TKS2 (shn ++ shp) x)
astReplicateNS shn v | STKS shp x <- ftkToSTK (ftkAst v) =
  let go :: ShS shn' -> AstTensor AstMethodLet s (TKS2 (shn' ++ shp) x)
      go ZSS = v
      go ((:$$) @k SNat shn2) =
        astReplicate (SNat @k) (STKS (shn2 `shsAppend` shp) x) $ go shn2
  in go shn


-- * A cheap simplification of only the topmost nodes

-- This does a single step of simplification of any non-indexing term
-- (many steps if guaranteed net beneficial). Terms representing integers
-- and and AstBool terms are simplified as much as possible.
astNonIndexStep
  :: AstSpan s
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
astNonIndexStep t = case t of
  Ast.AstPair t1 t2 -> astPair (astNonIndexStep t1) (astNonIndexStep t2)
  Ast.AstProject1 u -> astProject1 u
  Ast.AstProject2 u -> astProject2 u
  Ast.AstFromVector snat stk l -> astFromVector snat stk l
  Ast.AstSum snat stk v -> astSum snat stk v
  Ast.AstReplicate snat stk v -> astReplicate snat stk v
  Ast.AstMapAccumRDer k bShs eShs f df rf acc0 es ->
    astMapAccumRDer k bShs eShs f df rf acc0 es
  Ast.AstMapAccumLDer k bShs eShs f df rf acc0 es ->
    astMapAccumLDer k bShs eShs f df rf acc0 es
  Ast.AstApply stk v ll -> astApply stk v ll
  Ast.AstVar{} -> t
  Ast.AstCond a b c -> astCond a b c
  Ast.AstBuild1{} -> t
  AstConcrete repF -> astConcrete repF

  Ast.AstLet var u v -> astLet var u v

  Ast.AstPrimalPart v -> astPrimalPart v  -- has to be done sooner or later
  Ast.AstDualPart v -> astDualPart v
  Ast.AstFromPrimal{} -> t
  Ast.AstFromDual{} -> t

  AstSumOfList args ->
    case isTensorInt t of
      Just Refl -> foldr1 contractAstPlusOp args
      _ -> astSumOfList args

  AstN1K opCode u ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp1 opCode u
      _ -> t
  AstN2K opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp2 opCode u v
      _ -> t
  Ast.AstR1K{} -> t
  Ast.AstR2K{} -> t
  Ast.AstI2K opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstIntegralOp2 opCode u v
      _ -> t
  Ast.AstFloorK{} -> t
  Ast.AstFromIntegralK v -> astFromIntegralK v
  Ast.AstCastK v -> astCastK v

  AstN1S{} -> t
  AstN2S{} -> t
  Ast.AstR1S{} -> t
  Ast.AstR2S{} -> t
  Ast.AstI2S{} -> t
  Ast.AstFloorS{} -> t
  Ast.AstFromIntegralS v -> astFromIntegralS v
  Ast.AstCastS v -> astCastS v

  Ast.AstIndexS{} -> t  -- was supposed to be *non*-index
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    astScatterS @shm @shn @shp shn v (vars, ix)
  Ast.AstGatherS shn v0 (ZS, ix) ->
    Ast.AstIndexS shn v0 ix
  Ast.AstGatherS @shm @shn @shp _shn v0 (vars, ZIS) ->
    astReplicateNS @shm @(shp ++ shn) (listsToShS vars) v0
  Ast.AstGatherS{} -> t  -- this is "index" enough
  Ast.AstMinIndexS{} -> t
  Ast.AstMaxIndexS{} -> t
  Ast.AstIotaS{} -> t
  Ast.AstAppendS x y -> astAppendS x y
  Ast.AstSliceS i n k v -> astSliceS i n k v
  Ast.AstReverseS v -> astReverseS v
  Ast.AstTransposeS perm v -> astTransposeS perm v
  Ast.AstReshapeS sh v -> astReshapeS sh v
  Ast.AstZipS _ -> t
  Ast.AstUnzipS _ -> t
  Ast.AstNestS sh1 sh2 v -> astNestS sh1 sh2 v
  Ast.AstUnNestS v -> astUnNestS v

  Ast.AstFromS stkz v -> astFromS stkz v
  Ast.AstSFromK u -> astSFromK $ astNonIndexStep u
  Ast.AstSFromR sh v -> astSFromR sh v
  Ast.AstSFromX sh v -> astSFromX sh v

  -- These should not appear here unless via wacky tests.
  Ast.AstReplicate0NS{} -> t
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatvecmulS{} -> t
  Ast.AstMatmul2S{} -> t


-- * The expansion (e.g., into gather expressions) bottom-up pass

expandAstInt :: AstInt AstMethodLet -> AstInt AstMethodLet
expandAstInt = expandAst

expandAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
expandAstIxS = fmap expandAstInt

expandAst
  :: forall s y. AstSpan s
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
expandAst t = case t of
  Ast.AstPair t1 t2 -> astPair (expandAst t1) (expandAst t2)
  Ast.AstProject1 v -> astProject1 (expandAst v)
  Ast.AstProject2 v -> astProject2 (expandAst v)
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map expandAst l)
  Ast.AstSum snat stk v -> astSum snat stk (expandAst v)
  Ast.AstReplicate snat stk v -> astReplicate snat stk (expandAst v)
  Ast.AstMapAccumRDer k bShs eShs f df rf acc0 es ->
    astMapAccumRDer k bShs eShs
                    (expandAstHFun f)
                    (expandAstHFun df)
                    (expandAstHFun rf)
                    (expandAst acc0)
                    (expandAst es)
  Ast.AstMapAccumLDer k bShs eShs f df rf acc0 es ->
    astMapAccumLDer k bShs eShs
                    (expandAstHFun f)
                    (expandAstHFun df)
                    (expandAstHFun rf)
                    (expandAst acc0)
                    (expandAst es)
  Ast.AstApply stk v ll -> astApply stk (expandAstHFun v) (expandAst ll)
  Ast.AstVar{} -> t
  Ast.AstCond b a2 a3 ->
    astCond (expandAstBool b) (expandAst a2) (expandAst a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = expandAst v
    in Ast.AstBuild1 k stk (var, v2)
  AstConcrete repF -> astConcrete repF

  Ast.AstLet var u v -> astLet var (expandAst u) (expandAst v)

  Ast.AstPrimalPart v -> astPrimalPart (expandAst v)
  Ast.AstDualPart v -> astDualPart (expandAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (expandAst v)
  Ast.AstFromDual v -> Ast.AstFromDual (expandAst v)

  AstSumOfList args ->
    case isTensorInt t of
      Just Refl -> foldr1 contractAstPlusOp (NonEmpty.map expandAst args)
      _ -> astSumOfList (NonEmpty.map expandAst args)

  AstN1K opCode u ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp1 opCode (expandAst u)
      _ -> AstN1K opCode (expandAst u)
  AstN2K opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp2 opCode (expandAst u) (expandAst v)
      _ -> {- TODO: case opCode of
        TimesOp | Just Refl <- sameNat (Proxy @n) (Proxy @3) ->
          AstN2R opCode (simplifyAst u) (simplifyAst v)
            -- TODO: a workaround for interpretMatmul2 not yet generalized
            -- to gathers (and moved from AstInterpret here, ideally)
        _ -> -} AstN2K opCode (expandAst u) (expandAst v)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (expandAst u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (expandAst u) (expandAst v)
  Ast.AstI2K opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstIntegralOp2 opCode (expandAst u) (expandAst v)
      _ -> Ast.AstI2K opCode (expandAst u) (expandAst v)
  Ast.AstFloorK a -> Ast.AstFloorK (expandAst a)
  Ast.AstFromIntegralK v -> astFromIntegralK $ expandAst v
  Ast.AstCastK v -> astCastK $ expandAst v

  AstN1S opCode u -> AstN1S opCode (expandAst u)
  AstN2S opCode u v -> AstN2S opCode (expandAst u) (expandAst v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (expandAst u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (expandAst u) (expandAst v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (expandAst u) (expandAst v)
  Ast.AstFloorS a -> Ast.AstFloorS (expandAst a)
  Ast.AstFromIntegralS v -> astFromIntegralS $ expandAst v
  Ast.AstCastS v -> astCastS $ expandAst v

  Ast.AstIndexS shn v ix ->
    astIndexKnobsS (defaultKnobs {knobExpand = True})
                   shn
                   (expandAst v)
                   (expandAstIxS ix)
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    astScatterS @shm @shn @shp shn (expandAst v) (vars, expandAstIxS ix)
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    astGatherKnobsS @shm @shn @shp
                    (defaultKnobs {knobExpand = True})
                    shn (expandAst v) (vars, expandAstIxS ix)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (expandAst a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (expandAst a)
  Ast.AstIotaS{} -> t
  Ast.AstAppendS x y -> astAppendS (expandAst x) (expandAst y)
  Ast.AstSliceS i n k v -> astSliceS i n k (expandAst v)
  Ast.AstReverseS v -> astReverseS (expandAst v)
  Ast.AstTransposeS perm v -> case v of
    Ast.AstVar{} -> t  -- normal form
    Ast.AstPrimalPart Ast.AstVar{} -> t  -- normal form
    Ast.AstDualPart Ast.AstVar{} -> t  -- normal form
    Ast.AstFromPrimal Ast.AstVar{} -> t  -- normal form
    Ast.AstFromDual Ast.AstVar{} -> t  -- normal form
    Ast.AstProject1 Ast.AstVar{} -> t  -- normal form
    Ast.AstProject2 Ast.AstVar{} -> t  -- normal form
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
    Ast.AstScatterS _ _ (_, ix)
     | gcompare (Permutation.permRank perm) (ixsRank ix) == GGT -> t  -- nf
    Ast.AstSFromR{} -> t  -- normal form
    Ast.AstSFromX{} -> t  -- normal form
    _ ->  -- not nf, let's express all as a gather
      astTransposeAsGatherS (defaultKnobs {knobExpand = True})
                            perm  -- TODO: (normalizePermutation perm)
                            (expandAst v)
        -- this is expensive but the only way to guarantee full simplification
  Ast.AstReshapeS sh v -> case v of
    Ast.AstVar{} -> t  -- normal form
    Ast.AstPrimalPart Ast.AstVar{} -> t  -- normal form
    Ast.AstDualPart Ast.AstVar{} -> t  -- normal form
    Ast.AstFromPrimal Ast.AstVar{} -> t  -- normal form
    Ast.AstFromDual Ast.AstVar{} -> t  -- normal form
    Ast.AstProject1 Ast.AstVar{} -> t  -- normal form
    Ast.AstProject2 Ast.AstVar{} -> t  -- normal form
    AstSumOfList{} -> t  -- normal form
    AstN1S _ w | isVar w -> t  -- normal form
    AstN2S _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstR1S _ w | isVar w -> t  -- normal form
    Ast.AstR2S _ x y | isVar x && isVar y -> t  -- normal form
    Ast.AstScatterS{} -> t  -- normal form
    Ast.AstSFromR{} -> t  -- normal form
    Ast.AstSFromX{} -> t  -- normal form
    _ ->  -- not nf, let's express all as a gather
      astReshapeAsGatherS (defaultKnobs {knobExpand = True})
                          sh (expandAst v)
        -- this is expensive but the only way to guarantee full simplification
  Ast.AstZipS v -> Ast.AstZipS (expandAst v)
  Ast.AstUnzipS v -> Ast.AstUnzipS (expandAst v)
  Ast.AstNestS sh1 sh2 v ->
    astNestS sh1 sh2 $ expandAst v
  Ast.AstUnNestS v -> astUnNestS $ expandAst v

  Ast.AstFromS stkz v -> astFromS stkz $ expandAst v
  Ast.AstSFromK u -> astSFromK $ expandAst u
  Ast.AstSFromR sh v -> astSFromR sh $ expandAst v
  Ast.AstSFromX sh v -> astSFromX sh $ expandAst v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstReplicate0NS{} -> t
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatvecmulS{} -> t
  Ast.AstMatmul2S{} -> t

expandAstHFun :: AstHFun x y -> AstHFun x y
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
  Ast.AstRel opCodeRel arg1 arg2 ->
    case ftkToSTK (ftkAst arg1) of
      STKScalar ->
        contractRelOp opCodeRel (expandAst arg1) (expandAst arg2)
          -- Because the scalar tensors sometimes represent indexes,
          -- we expand them a bit more than all the others.
      _ -> Ast.AstRel opCodeRel (expandAst arg1) (expandAst arg2)


-- * The simplifying bottom-up pass

simplifyAstInt :: AstInt AstMethodLet -> AstInt AstMethodLet
simplifyAstInt = simplifyAst

simplifyAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
simplifyAstIxS = fmap simplifyAstInt

-- | This function guarantees full simplification: every redex
-- is visited and each combinator applied. The most exhaustive and costly
-- variants of each combinator are used, e.g., astIndexR.
simplifyAst
  :: forall s y. AstSpan s
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
simplifyAst t = case t of
  Ast.AstPair t1 t2 -> astPair (simplifyAst t1) (simplifyAst t2)
  Ast.AstProject1 v -> astProject1 (simplifyAst v)
  Ast.AstProject2 v -> astProject2 (simplifyAst v)
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map simplifyAst l)
  Ast.AstSum snat stk v -> astSum snat stk (simplifyAst v)
  Ast.AstReplicate snat stk v ->  astReplicate snat stk (simplifyAst v)
  Ast.AstMapAccumRDer k bShs eShs f df rf acc0 es ->
    astMapAccumRDer k bShs eShs
                    (simplifyAstHFun f)
                    (simplifyAstHFun df)
                    (simplifyAstHFun rf)
                    (simplifyAst acc0)
                    (simplifyAst es)
  Ast.AstMapAccumLDer k bShs eShs f df rf acc0 es ->
    astMapAccumLDer k bShs eShs
                    (simplifyAstHFun f)
                    (simplifyAstHFun df)
                    (simplifyAstHFun rf)
                    (simplifyAst acc0)
                    (simplifyAst es)
  Ast.AstApply stk v ll -> astApply stk (simplifyAstHFun v) (simplifyAst ll)
  Ast.AstVar{} -> t
  Ast.AstCond b a2 a3 ->
    astCond (simplifyAstBool b) (simplifyAst a2) (simplifyAst a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = simplifyAst v
    in Ast.AstBuild1 k stk (var, v2)
  AstConcrete repF -> astConcrete repF

  Ast.AstLet var u v -> astLet var (simplifyAst u) (simplifyAst v)

  Ast.AstPrimalPart v -> astPrimalPart (simplifyAst v)
  Ast.AstDualPart v -> astDualPart (simplifyAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (simplifyAst v)
  Ast.AstFromDual v -> Ast.AstFromDual (simplifyAst v)

  AstSumOfList args ->
    case isTensorInt t of
      Just Refl -> foldr1 contractAstPlusOp (NonEmpty.map simplifyAst args)
      _ -> astSumOfList (NonEmpty.map simplifyAst args)

  AstN1K opCode u ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp1 opCode (simplifyAst u)
      _ -> AstN1K opCode (simplifyAst u)
  AstN2K opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp2 opCode (simplifyAst u) (simplifyAst v)
      _ -> AstN2K opCode (simplifyAst u) (simplifyAst v)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (simplifyAst u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2K opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstIntegralOp2 opCode (simplifyAst u) (simplifyAst v)
      _ -> Ast.AstI2K opCode (simplifyAst u) (simplifyAst v)
  Ast.AstFloorK a -> Ast.AstFloorK (simplifyAst a)
  Ast.AstFromIntegralK v -> astFromIntegralK $ simplifyAst v
  Ast.AstCastK v -> astCastK $ simplifyAst v

  AstN1S opCode u -> AstN1S opCode (simplifyAst u)
  AstN2S opCode u v -> AstN2S opCode (simplifyAst u) (simplifyAst v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (simplifyAst u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (simplifyAst u) (simplifyAst v)
  Ast.AstFloorS a -> Ast.AstFloorS (simplifyAst a)
  Ast.AstFromIntegralS v -> astFromIntegralS $ simplifyAst v
  Ast.AstCastS v -> astCastS $ simplifyAst v

  Ast.AstIndexS shn v ix ->
    astIndexS shn (simplifyAst v) (simplifyAstIxS ix)
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    astScatterS @shm @shn @shp shn (simplifyAst v) (vars, simplifyAstIxS ix)
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    astGatherS @shm @shn @shp shn (simplifyAst v) (vars, simplifyAstIxS ix)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (simplifyAst a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (simplifyAst a)
  Ast.AstIotaS{} -> t
  Ast.AstAppendS x y -> astAppendS (simplifyAst x) (simplifyAst y)
  Ast.AstSliceS i n k v -> astSliceS i n k (simplifyAst v)
  Ast.AstReverseS v -> astReverseS (simplifyAst v)
  Ast.AstTransposeS perm v -> astTransposeS perm $ simplifyAst v  -- TODO:(normalizePermutation perm)
  Ast.AstReshapeS sh v -> astReshapeS sh $ simplifyAst v
  Ast.AstZipS v -> Ast.AstZipS (simplifyAst v)
  Ast.AstUnzipS v -> Ast.AstUnzipS (simplifyAst v)
  Ast.AstNestS sh1 sh2 v ->
    astNestS sh1 sh2 $ simplifyAst v
  Ast.AstUnNestS v -> astUnNestS $ simplifyAst v

  Ast.AstFromS stkz v -> astFromS stkz $ simplifyAst v
  Ast.AstSFromK u -> astSFromK $ simplifyAst u
  Ast.AstSFromR sh v -> astSFromR sh $ simplifyAst v
  Ast.AstSFromX sh v -> astSFromX sh $ simplifyAst v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstReplicate0NS{} -> t
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatvecmulS{} -> t
  Ast.AstMatmul2S{} -> t

simplifyAstHFun :: AstHFun x y -> AstHFun x y
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
  Ast.AstRel opCodeRel arg1 arg2 ->
    case ftkToSTK (ftkAst arg1) of
      STKScalar ->
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
-- TODO: Generalize some of the extra term constructors and the rules.

contractAstInt :: AstInt AstMethodLet -> AstInt AstMethodLet
contractAstInt = contractAst

contractAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
contractAstIxS = fmap contractAstInt

contractAst
  :: forall s y. AstSpan s
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
contractAst t = case t of
  Ast.AstPair t1 t2 -> astPair (contractAst t1) (contractAst t2)
  Ast.AstProject1 v -> astProject1 (contractAst v)
  Ast.AstProject2 v -> astProject2 (contractAst v)
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map contractAst l)
  Ast.AstSum snat stk (AstN2S TimesOp
                         (Ast.AstLet vart vt (Ast.AstTransposeS tperm t2))
                         (Ast.AstTransposeS uperm u)) ->
      (Ast.AstLet
         vart
         (contractAst vt)
         (contractAst $ Ast.AstSum  -- the crucial exposed redex
            snat stk (AstN2S
                        TimesOp
                        (Ast.AstTransposeS tperm (contractAst t2))
                        (Ast.AstTransposeS uperm (contractAst u)))))
  Ast.AstSum snat stk (AstN2S TimesOp
                         (Ast.AstTransposeS tperm t2)
                         (Ast.AstLet varu vu (Ast.AstTransposeS uperm u))) ->
      (Ast.AstLet
         varu
         (contractAst vu)
         (contractAst $ Ast.AstSum  -- the crucial exposed redex
            snat stk (AstN2S
                        TimesOp
                        (Ast.AstTransposeS tperm (contractAst t2))
                        (Ast.AstTransposeS uperm (contractAst u)))))
  Ast.AstSum snat stk (AstN2S TimesOp
                         (Ast.AstLet vart vt (Ast.AstTransposeS tperm t2))
                         (Ast.AstLet varu vu (Ast.AstTransposeS uperm u))) ->
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
  Ast.AstSum
    snat@(SNat @m2)
    stk@(STKS (SNat @n2 :$$ SNat @p2 :$$ ZSS) (STKScalar @r))
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
          in case testEquality (typeRep @r) (typeRep @Double) of
            Just Refl ->
              Just $ Ast.AstMatmul2S
                       (SNat @m') (SNat @n') (SNat @p') t4 u4
            _ -> case testEquality (typeRep @r) (typeRep @Float) of
              Just Refl ->
                Just $ Ast.AstMatmul2S
                         (SNat @m') (SNat @n') (SNat @p') t4 u4
              _ -> case testEquality (typeRep @r) (typeRep @Int64) of
                Just Refl ->
                  Just $ Ast.AstMatmul2S
                           (SNat @m') (SNat @n') (SNat @p') t4 u4
                _ -> case testEquality (typeRep @r) (typeRep @CInt) of
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
  Ast.AstSum SNat (STKS ZSS _) (AstN2S TimesOp t2 u) ->
    Ast.AstDot0S (contractAst t2) (contractAst u)
  Ast.AstSum _ (STKS ZSS _) (Ast.AstReshapeS _ (AstN2S TimesOp t2 u)) ->
    Ast.AstDot0S (contractAst t2) (contractAst u)
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
  Ast.AstSum
    snat stk@(STKS ZSS _) (Ast.AstReshapeS
                             @sh3 @sh sh (Ast.AstTransposeS @_ @sh2 _ t2)) ->
    gcastWith (unsafeCoerceRefl :: Product sh2 :~: Product sh3) $
    contractAst (Ast.AstSum snat stk (Ast.AstReshapeS @sh2 @sh sh t2))
  Ast.AstSum snat stk@(STKS ZSS _) (Ast.AstReshapeS
                                      @_ @sh sh (Ast.AstReverseS t2)) ->
    contractAst (Ast.AstSum snat stk (Ast.AstReshapeS @_ @sh sh t2))
  Ast.AstSum _k1 (STKS ZSS _) (Ast.AstReshapeS _sh (Ast.AstSum SNat _ t2)) ->
    Ast.AstSum0S (contractAst t2)
  Ast.AstSum SNat (STKS ZSS _) (Ast.AstSum SNat _ t2) ->
    Ast.AstSum0S (contractAst t2)
      -- TODO: more cases are needed
  Ast.AstSum snat stk (Ast.AstLet var v t2) ->
    contractAst (Ast.AstLet var v (Ast.AstSum snat stk t2))
  Ast.AstSum snat stk (Ast.AstReshapeS @sh sh (Ast.AstLet var v t2)) ->
    contractAst
      (Ast.AstLet var v (Ast.AstSum snat stk (Ast.AstReshapeS @sh sh t2)))
  Ast.AstSum _ (STKS ZSS _) (Ast.AstReshapeS _sh t2) ->
    Ast.AstSum0S (contractAst t2)
  Ast.AstSum snat stk v -> astSum snat stk (contractAst v)
  Ast.AstReplicate snat stk v -> astReplicate snat stk (contractAst v)
  Ast.AstMapAccumRDer k bShs eShs f df rf acc0 es ->
    astMapAccumRDer k bShs eShs
                    (contractAstHFun f)
                    (contractAstHFun df)
                    (contractAstHFun rf)
                    (contractAst acc0)
                    (contractAst es)
  Ast.AstMapAccumLDer k bShs eShs f df rf acc0 es ->
    astMapAccumLDer k bShs eShs
                    (contractAstHFun f)
                    (contractAstHFun df)
                    (contractAstHFun rf)
                    (contractAst acc0)
                    (contractAst es)
  Ast.AstApply stk v ll -> astApply stk (contractAstHFun v) (contractAst ll)
  Ast.AstVar{} -> t
  Ast.AstCond b a2 a3 ->
    astCond (contractAstBool b) (contractAst a2) (contractAst a3)
  -- These are only needed for tests that don't vectorize Ast.
  Ast.AstBuild1 snat stk (var, Ast.AstSum
                             n _
                             (AstN2S
                                TimesOp
                                t2
                                (Ast.AstIndexS _shn
                                   u (((:.$) @m (AstIntVar var2) ZIS)))))
    | STKS ZSS _ <- stk
    , Just Refl <- testEquality snat (SNat @m)
    , var == var2
    , not (varNameInAst var t2),  not (varNameInAst var u) ->
        Ast.AstMatvecmulS snat n (contractAst u) (contractAst t2)
  Ast.AstBuild1
    snat stk (var, Ast.AstSum _ _
                     (Ast.AstReshapeS
                        _sh (AstN2S
                               TimesOp
                               t2
                               (Ast.AstIndexS _shn
                                  u (((:.$) @m (AstIntVar var2) ZIS))))))
    | STKS ZSS _ <- stk
    , STKS (n :$$ ZSS) _ <- ftkToSTK (ftkAst t2)
    , Just Refl <- testEquality snat (SNat @m)
    , var == var2
    , not (varNameInAst var t2),  not (varNameInAst var u) ->
        Ast.AstMatvecmulS snat n (contractAst u) (contractAst t2)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = contractAst v
    in Ast.AstBuild1 k stk (var, v2)
  AstConcrete repF -> astConcrete repF

  Ast.AstLet var u v -> astLet var (contractAst u) (contractAst v)

  Ast.AstPrimalPart v -> astPrimalPart (contractAst v)
  Ast.AstDualPart v -> astDualPart (contractAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (contractAst v)
  Ast.AstFromDual v -> Ast.AstFromDual (contractAst v)

  AstSumOfList args ->
    case isTensorInt t of
      Just Refl -> foldr1 contractAstPlusOp (NonEmpty.map contractAst args)
      _ -> astSumOfList (NonEmpty.map contractAst args)

  AstN1K opCode u ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp1 opCode (contractAst u)
      _ -> AstN1K opCode (contractAst u)
  AstN2K opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstNumOp2 opCode (contractAst u) (contractAst v)
      _ -> AstN2K opCode (contractAst u) (contractAst v)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (contractAst u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (contractAst u) (contractAst v)
  Ast.AstI2K opCode u v ->
    case isTensorInt u of
      Just Refl -> contractAstIntegralOp2 opCode (contractAst u) (contractAst v)
      _ -> Ast.AstI2K opCode (contractAst u) (contractAst v)
  Ast.AstFloorK a -> Ast.AstFloorK (contractAst a)
  Ast.AstFromIntegralK v -> astFromIntegralK $ contractAst v
  Ast.AstCastK v -> astCastK $ contractAst v

  AstN1S opCode u -> AstN1S opCode (contractAst u)
  AstN2S TimesOp v (Ast.AstLet var u
                      (Ast.AstReshapeS @_ @sh sh
                         (Ast.AstReplicate (SNat @m) stk s)))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v) ->
        -- The varNameInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        Ast.AstLet
          var
          (contractAst u)
          (AstN2S
             TimesOp v (Ast.AstReshapeS @_ @sh sh
                          (Ast.AstReplicate
                             (SNat @m) stk (contractAst s))))
  AstN2S TimesOp v (Ast.AstReshapeS @_ @sh sh
                      (Ast.AstLet
                         var u (Ast.AstReplicate (SNat @m) stk s)))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v) ->
      Ast.AstLet var
                 (contractAst u)
                 (AstN2S TimesOp
                    v (astReshapeS @_ @sh sh
                         (Ast.AstReplicate
                           (SNat @m) stk (contractAst s))))
  AstN2S TimesOp v (Ast.AstLet var u (Ast.AstReplicate (SNat @m) stk s))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v) ->
      Ast.AstLet var
                 (contractAst u)
                 (AstN2S TimesOp v (Ast.AstReplicate
                                     (SNat @m) stk (contractAst s)))
  AstN2S opCode u v -> AstN2S opCode (contractAst u) (contractAst v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (contractAst u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (contractAst u) (contractAst v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (contractAst u) (contractAst v)
  Ast.AstFloorS a -> Ast.AstFloorS (contractAst a)
  Ast.AstFromIntegralS v -> astFromIntegralS $ contractAst v
  Ast.AstCastS v -> astCastS $ contractAst v

  Ast.AstIndexS _shn Ast.AstIotaS{} (i :.$ ZIS) ->
    astFromIntegralS $ astSFromK $ contractAstInt i
  Ast.AstIndexS shn v ix ->
    astIndexS shn (contractAst v) (contractAstIxS ix)
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    astScatterS @shm @shn @shp shn (contractAst v) (vars, contractAstIxS ix)
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    astGatherS @shm @shn @shp shn (contractAst v) (vars, contractAstIxS ix)
{- TODO, but sbuild is tricky, so only if benchmarks show it's worth it:
  AstGatherS @shm AstIotaS (vars, i :.$ ZIS) | Refl <- lemAppNil @shm ->
    gcastWith (unsafeCoerceRefl :: Drop (Rank shm) shm :~: '[]) $
    gcastWith (unsafeCoerceRefl :: Take (Rank shm) shm :~: shm) $
    sbuild @_ @_ @(Rank shm)
           (interpretLambdaIndexS
              interpretAst env
              (vars, fromPrimal @s $ AstFromIntegralS $ AstSFromK i)) -}
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (contractAst a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (contractAst a)
  Ast.AstIotaS{} -> t
  Ast.AstAppendS x y -> astAppendS (contractAst x) (contractAst y)
  Ast.AstSliceS i n k v -> astSliceS i n k (contractAst v)
  Ast.AstReverseS v -> astReverseS (contractAst v)
  Ast.AstTransposeS perm v -> astTransposeS perm $ contractAst v  -- TODO:(normalizePermutation perm)
  Ast.AstReshapeS sh (Ast.AstReplicate _ (STKS ZSS _) s) ->
    Ast.AstReplicate0NS sh (contractAst s)
      -- TODO: maybe move this and others to astReshape and maybe somehow join
      -- with astReplicate0NS and also do this in this case and others:
      -- Ast.AstReplicate _ (STKR @m _ STKScalar) x
      --    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
      --      astReplicate0N shOut x
  Ast.AstReshapeS sh (Ast.AstLet var v (Ast.AstReplicate snat stk t2)) ->
    Ast.AstLet var
               (contractAst v)
               (astReshapeS sh (Ast.AstReplicate snat stk (contractAst t2)))
  Ast.AstReshapeS sh v -> astReshapeS sh $ contractAst v
  Ast.AstZipS v -> Ast.AstZipS (contractAst v)
  Ast.AstUnzipS v -> Ast.AstUnzipS (contractAst v)
  Ast.AstNestS sh1 sh2 v ->
    astNestS sh1 sh2 $ contractAst v
  Ast.AstUnNestS v -> astUnNestS $ contractAst v

  Ast.AstFromS stkz v -> astFromS stkz $ contractAst v
  Ast.AstSFromK u -> astSFromK $ contractAst u
  Ast.AstSFromR sh v -> astSFromR sh $ contractAst v
  Ast.AstSFromX sh v -> astSFromX sh $ contractAst v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstReplicate0NS{} -> t
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatvecmulS{} -> t
  Ast.AstMatmul2S{} -> t

contractAstHFun :: AstHFun x y -> AstHFun x y
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
  Ast.AstRel opCodeRel arg1 arg2 ->
    case ftkToSTK (ftkAst arg1) of
      STKScalar ->
        contractRelOp opCodeRel (contractAst arg1) (contractAst arg2)
      _ -> Ast.AstRel opCodeRel (contractAst arg1) (contractAst arg2)


-- * Contraction of arithmetic and boolean operations

contractRelOp :: GoodScalar r
              => OpCodeRel
              -> AstTensor AstMethodLet PrimalSpan (TKScalar r)
              -> AstTensor AstMethodLet PrimalSpan (TKScalar r)
              -> AstBool AstMethodLet
contractRelOp EqOp (AstConcrete (RepF _ u)) (AstConcrete (RepF _ v)) =
  AstBoolConst $ u == v
contractRelOp NeqOp (AstConcrete (RepF _ u)) (AstConcrete (RepF _ v)) =
  AstBoolConst $ u /= v
contractRelOp LeqOp (AstConcrete (RepF _ u)) (AstConcrete (RepF _ v)) =
  AstBoolConst $ u <= v
contractRelOp GeqOp (AstConcrete (RepF _ u)) (AstConcrete (RepF _ v)) =
  AstBoolConst $ u >= v
contractRelOp LsOp (AstConcrete (RepF _ u)) (AstConcrete (RepF _ v)) =
  AstBoolConst $ u < v
contractRelOp GtOp (AstConcrete (RepF _ u)) (AstConcrete (RepF _ v)) =
  AstBoolConst $ u > v
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
contractAstPlusOp (AstSumOfList (AstConcrete (RepF _ u) :| lu))
                  (AstSumOfList (AstConcrete (RepF _ v) :| lv)) =
  addConstToList (u + v) (lu ++ lv)
contractAstPlusOp (AstSumOfList lu)
                  (AstSumOfList (AstConcrete (RepF ftk v) :| lv)) =
  AstSumOfList ((AstConcrete (RepF ftk v) :| lv) <> lu)
contractAstPlusOp (AstSumOfList lu)
                  (AstSumOfList lv) =
  AstSumOfList (lu <> lv)

contractAstPlusOp (AstConcrete (RepF _ u))
                  (AstSumOfList (AstConcrete (RepF _ v) :| lv)) =
  addConstToList (u + v) lv
contractAstPlusOp u (AstSumOfList (AstConcrete (RepF ftk v) :| lv)) =
  AstSumOfList (AstConcrete (RepF ftk v) :| u : lv)
contractAstPlusOp u (AstSumOfList lv) =
  AstSumOfList (u NonEmpty.<| lv)

contractAstPlusOp (AstSumOfList (AstConcrete (RepF _ u) :| lu))
                  (AstConcrete (RepF _ v)) =
  addConstToList (u + v) lu
contractAstPlusOp (AstSumOfList (AstConcrete (RepF ftk u) :| lu))
                  v =
  AstSumOfList (AstConcrete (RepF ftk u) :| v : lu)
contractAstPlusOp (AstSumOfList lu)
                  v =
  AstSumOfList (v NonEmpty.<| lu)

contractAstPlusOp (AstConcrete (RepF ftk u)) (AstConcrete (RepF _ v)) =
  AstConcrete (RepF ftk (u + v))
contractAstPlusOp u (AstConcrete (RepF _ v)) = addConstToList v [u]
contractAstPlusOp (AstConcrete (RepF _ u)) v = addConstToList u [v]

-- Unfortunately, these won't fire if the required terms are scattered
-- among elements of the AstSumOfList list. However, in many cases,
-- binary addition is used interspersed with other operations,
-- so longer lists don't form and so these terms have a chance to be adjacent,
-- especially that AstConcrete is guaranteed not to intervene.
contractAstPlusOp (AstN1K NegateOp (Ast.AstVar _ var))
                  (Ast.AstVar _ var')
  | var == var' = 0
contractAstPlusOp (Ast.AstVar _ var')
                  (AstN1K NegateOp (Ast.AstVar _ var))
  | var == var' = 0
contractAstPlusOp
  (Ast.AstI2K RemOp (AstN1K NegateOp (Ast.AstVar _ var)) (AstConcrete (RepF _ v)))
  (Ast.AstI2K RemOp (Ast.AstVar _ var') (AstConcrete (RepF _ v')))
  | var == var' && v == v' = 0
contractAstPlusOp
  (Ast.AstI2K RemOp (Ast.AstVar _ var') (AstConcrete (RepF _ v')))
  (Ast.AstI2K RemOp (AstN1K NegateOp (Ast.AstVar _ var)) (AstConcrete (RepF _ v)))
  | var == var' && v == v' = 0

contractAstPlusOp u v = AstSumOfList (u :| [v])

addConstToList :: RepN (TKScalar Int64) -> [AstInt AstMethodLet]
               -> AstInt AstMethodLet
addConstToList a [] = AstConcrete (RepF FTKScalar a)
addConstToList !a [!i] =
  if unRepN a == 0
  then i
  else AstSumOfList (AstConcrete (RepF FTKScalar a) :| [i])
addConstToList a l@(b : rest) =
  if unRepN a == 0
  then AstSumOfList (b :| rest)
  else AstSumOfList (AstConcrete (RepF FTKScalar a) :| l)

contractAstNumOp1 :: OpCodeNum1 -> AstInt AstMethodLet -> AstInt AstMethodLet
contractAstNumOp1 NegateOp (AstConcrete (RepF ftk u)) = AstConcrete (RepF ftk (negate u))
contractAstNumOp1 NegateOp (AstSumOfList l) =
  foldr1 contractAstPlusOp $ NonEmpty.map (contractAstNumOp1 NegateOp) l
contractAstNumOp1 NegateOp (AstN2K TimesOp (AstConcrete (RepF ftk u)) v) =
  contractAstNumOp2 TimesOp (AstConcrete (RepF ftk (negate u))) v
    -- given a choice, prefer to negate a constant
contractAstNumOp1 NegateOp (AstN2K TimesOp u v) =
  contractAstNumOp2 TimesOp u (contractAstNumOp1 NegateOp v)
contractAstNumOp1 NegateOp (AstN1K NegateOp u) = u
contractAstNumOp1 NegateOp (AstN1K SignumOp u) =
  contractAstNumOp1 SignumOp (contractAstNumOp1 NegateOp u)
contractAstNumOp1 NegateOp (Ast.AstI2K QuotOp u v) =
  contractAstIntegralOp2 QuotOp (contractAstNumOp1 NegateOp u) v
    -- v is likely positive and let's keep it so
contractAstNumOp1 NegateOp (Ast.AstI2K RemOp u v) =
  contractAstIntegralOp2 RemOp (contractAstNumOp1 NegateOp u) v
    -- v is likely positive and let's keep it so

contractAstNumOp1 AbsOp (AstConcrete (RepF ftk u)) = AstConcrete (RepF ftk (abs u))
contractAstNumOp1 AbsOp (AstN1K AbsOp u) = AstN1K AbsOp u
contractAstNumOp1 AbsOp (AstN1K NegateOp u) = contractAstNumOp1 AbsOp u
contractAstNumOp1 SignumOp (AstConcrete (RepF ftk u)) = AstConcrete (RepF ftk (signum u))
contractAstNumOp1 SignumOp (AstN1K SignumOp u) = AstN1K SignumOp u
contractAstNumOp1 SignumOp (AstN1K AbsOp u) =
  contractAstNumOp1 AbsOp (AstN1K SignumOp u)

contractAstNumOp1 opCode u = AstN1K opCode u

contractAstNumOp2 :: OpCodeNum2 -> AstInt AstMethodLet -> AstInt AstMethodLet
                  -> AstInt AstMethodLet
contractAstNumOp2 MinusOp u v =
  contractAstPlusOp u (contractAstNumOp1 NegateOp v)
contractAstNumOp2 TimesOp (AstConcrete (RepF ftk u)) (AstConcrete (RepF _ v)) =
  AstConcrete (RepF ftk (u * v))
contractAstNumOp2 TimesOp (AstConcrete (RepF ftk i)) _v | unRepN i == 0 =
  AstConcrete (RepF ftk i)
contractAstNumOp2 TimesOp _u (AstConcrete (RepF ftk i)) | unRepN i == 0 =
  AstConcrete (RepF ftk i)
contractAstNumOp2 TimesOp (AstConcrete (RepF _ i)) v | unRepN i == 1 = v
contractAstNumOp2 TimesOp u (AstConcrete (RepF _ i)) | unRepN i == 1 = u
{- TODO: is it worth adding AstLet with a fresh variables
   to share w and so make these rules safe? Perhaps after we decide
   a normal form (e.g., a polynomial)?
contractAstNumOp TimesOp (AstN2K PlusOp (u, v), w) =
  contractAstPlusOp ( contractAstNumOp TimesOp (u, w)
                    , contractAstNumOp TimesOp (v, w) )
contractAstNumOp TimesOp (u, AstN2K PlusOp (v, w)) =
  contractAstPlusOp ( contractAstNumOp TimesOp (u, v)
                    , contractAstNumOp TimesOp (u, w) )
-}
contractAstNumOp2 TimesOp (AstSumOfList l) w@AstConcrete{} =
  foldr1 contractAstPlusOp
  $ NonEmpty.map (\u -> contractAstNumOp2 TimesOp u w) l
contractAstNumOp2 TimesOp u@AstConcrete{} (AstSumOfList l) =
  foldr1 contractAstPlusOp
  $ NonEmpty.map (contractAstNumOp2 TimesOp u) l
-- TODO: perhaps aim for a polynomial normal form? but that requires global
-- inspection of the whole expression
contractAstNumOp2 TimesOp (AstConcrete (RepF ftk u))
                          (AstN2K TimesOp (AstConcrete (RepF _ v)) w) =
  contractAstNumOp2 TimesOp (AstConcrete (RepF ftk (u * v))) w
contractAstNumOp2 TimesOp u (AstConcrete (RepF ftk n)) =
  contractAstNumOp2 TimesOp (AstConcrete (RepF ftk n)) u
contractAstNumOp2 TimesOp (AstN2K TimesOp u v) w =
  contractAstNumOp2 TimesOp u (contractAstNumOp2 TimesOp v w)

-- With static shapes, the second argument to QuotOp and RemOp
-- is often a constant, which makes such rules worth including,
-- since they are likely to fire. To help them fire, we avoid changing
-- that constant, if possible, e.g., in rules for NegateOp.
contractAstNumOp2
  TimesOp (AstConcrete (RepF ftk v))
          (Ast.AstI2K QuotOp (Ast.AstVar ftk2 var)
                             (AstConcrete (RepF _ v'))) | v == v' =
    contractAstNumOp2 MinusOp
                      (Ast.AstVar ftk2 var)
                      (Ast.AstI2K RemOp (Ast.AstVar ftk2 var)
                                        (AstConcrete (RepF ftk v)))
contractAstNumOp2 opCode u v = AstN2K opCode u v

contractAstIntegralOp2 :: OpCodeIntegral2 -> AstInt AstMethodLet
                       -> AstInt AstMethodLet
                       -> AstInt AstMethodLet
contractAstIntegralOp2 QuotOp (AstConcrete (RepF ftk u)) (AstConcrete (RepF _ v)) = AstConcrete (RepF ftk (quotF u v))
contractAstIntegralOp2 QuotOp (AstConcrete (RepF ftk i)) _v | unRepN i == 0 = AstConcrete (RepF ftk i)
contractAstIntegralOp2 QuotOp u (AstConcrete (RepF _ i)) | unRepN i == 1 = u
contractAstIntegralOp2 QuotOp (Ast.AstI2K RemOp _u (AstConcrete (RepF _ v))) (AstConcrete (RepF _ v'))
  | v' >= v && v >= 0 = 0
contractAstIntegralOp2 QuotOp (Ast.AstI2K QuotOp u v) w =
  contractAstIntegralOp2 QuotOp u (contractAstNumOp2 TimesOp v w)
contractAstIntegralOp2 QuotOp (Ast.AstN2K TimesOp (AstConcrete (RepF _ u)) v) (AstConcrete (RepF _ u'))
  | u == u' = v

contractAstIntegralOp2 RemOp (AstConcrete (RepF ftk u)) (AstConcrete (RepF _ v)) = AstConcrete (RepF ftk (remF u v))
contractAstIntegralOp2 RemOp (AstConcrete (RepF ftk i)) _v | unRepN i == 0 = AstConcrete (RepF ftk i)
contractAstIntegralOp2 RemOp _u (AstConcrete (RepF ftk i)) | unRepN i == 1 = AstConcrete (RepF ftk (RepN 0))
contractAstIntegralOp2 RemOp (Ast.AstI2K RemOp u (AstConcrete (RepF ftk v))) (AstConcrete (RepF _ v'))
  | v' >= v && v >= 0 = Ast.AstI2K RemOp u (AstConcrete (RepF ftk v))
contractAstIntegralOp2 RemOp (Ast.AstI2K RemOp u (AstConcrete (RepF ftk v))) (AstConcrete (RepF _ v'))
  | remF v v' == 0 && v > 0 = contractAstIntegralOp2 RemOp u (AstConcrete (RepF ftk v'))
contractAstIntegralOp2 RemOp (AstN2K TimesOp (AstConcrete (RepF _ u)) _v) (AstConcrete (RepF _ u'))
  | remF u u' == 0 = 0

contractAstIntegralOp2 opCode u v = Ast.AstI2K opCode u v

-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right.
contractAstB2 :: OpCodeBool -> AstBool AstMethodLet -> AstBool AstMethodLet
              -> AstBool AstMethodLet
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

substituteAst :: forall s s2 y z. (AstSpan s, AstSpan s2)
              => AstTensor AstMethodLet s2 z -> AstVarName s2 z
              -> AstTensor AstMethodLet s y
              -> AstTensor AstMethodLet s y
substituteAst i var v1 =
  fromMaybe v1 $ substitute1Ast i var v1

substituteAstIxS
  :: AstSpan s
  => AstTensor AstMethodLet s y -> AstVarName s y -> AstIxS AstMethodLet sh
  -> AstIxS AstMethodLet sh
substituteAstIxS i var ix =
  fromMaybe ix $ substitute1AstIxS i var ix

substituteAstBool
  :: AstSpan s
  => AstTensor AstMethodLet s y -> AstVarName s y -> AstBool AstMethodLet
  -> AstBool AstMethodLet
substituteAstBool i var v1 =
  fromMaybe v1 $ substitute1AstBool i var v1


-- * Substitution workers

-- | We assume no variable is shared between a binding and its nested binding
-- and nobody substitutes into variables that are bound.
-- This keeps the substitution code simple, because we never need to compare
-- variables to any variable in the bindings.
substitute1Ast :: forall s s2 y z. (AstSpan s, AstSpan s2)
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
  Ast.AstFromVector snat stk args ->
    let margs = V.map (substitute1Ast i var) args
    in if V.any isJust margs
       then Just $ astFromVector snat stk $ V.zipWith fromMaybe args margs
       else Nothing
  Ast.AstSum snat stk v -> astSum snat stk <$> substitute1Ast i var v
  Ast.AstReplicate snat stk v ->
    astReplicate snat stk <$> substitute1Ast i var v
  Ast.AstMapAccumRDer k bShs eShs f df rf acc0 es ->
      case ( substitute1AstHFun i var f, substitute1AstHFun i var df
           , substitute1AstHFun i var rf, substitute1Ast i var acc0
           , substitute1Ast i var es ) of
        (Nothing, Nothing, Nothing, Nothing, Nothing) -> Nothing
        (mf, mdf, mrf, macc0, mes) ->
          Just $ astMapAccumRDer k bShs eShs
                                 (fromMaybe f mf)
                                 (fromMaybe df mdf)
                                 (fromMaybe rf mrf)
                                 (fromMaybe acc0 macc0)
                                 (fromMaybe es mes)
  Ast.AstMapAccumLDer k bShs eShs f df rf acc0 es ->
      case ( substitute1AstHFun i var f, substitute1AstHFun i var df
           , substitute1AstHFun i var rf, substitute1Ast i var acc0
           , substitute1Ast i var es ) of
        (Nothing, Nothing, Nothing, Nothing, Nothing) -> Nothing
        (mf, mdf, mrf, macc0, mes) ->
          Just $ astMapAccumLDer k bShs eShs
                                 (fromMaybe f mf)
                                 (fromMaybe df mdf)
                                 (fromMaybe rf mrf)
                                 (fromMaybe acc0 macc0)
                                 (fromMaybe es mes)
  Ast.AstApply stk t ll ->
    case ( substitute1AstHFun i var t
         , substitute1Ast i var ll ) of
      (Nothing, Nothing) -> Nothing
      (mt, mll) -> Just $ astApply stk (fromMaybe t mt) (fromMaybe ll mll)
  Ast.AstVar ftk var2 ->
    if varNameToAstVarId var == varNameToAstVarId var2
    then case sameAstSpan @s @s2 of
        Just Refl -> case matchingFTK (ftkAst i) ftk of
          Just Refl -> Just i
          _ -> error $ "substitute1Ast: kind of the variable "
                       ++ show var2 ++ ": " ++ show ftk
                       ++ ", payload kind: " ++ show (ftkAst i)
                       ++ ", payload: " ++ show i
        _ -> error "substitute1Ast: span"
    else Nothing
  Ast.AstCond b v w ->
    case ( substitute1AstBool i var b
         , substitute1Ast i var v
         , substitute1Ast i var w ) of
      (Nothing, Nothing, Nothing) -> Nothing
      (mb, mv, mw) ->
        Just $ astCond (fromMaybe b mb) (fromMaybe v mv) (fromMaybe w mw)
  Ast.AstBuild1 k stk (var2, v) ->
    assert (varNameToAstVarId var2 /= varNameToAstVarId var) $
    Ast.AstBuild1 k stk . (var2,) <$> substitute1Ast i var v
  Ast.AstConcrete{} -> Nothing

  Ast.AstLet var2 u v ->
    case (substitute1Ast i var u, substitute1Ast i var v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) -> Just $ astLet var2 (fromMaybe u mu) (fromMaybe v mv)

  Ast.AstPrimalPart a -> astPrimalPart <$> substitute1Ast i var a
  Ast.AstDualPart a -> astDualPart <$> substitute1Ast i var a
  Ast.AstFromPrimal a -> Ast.AstFromPrimal <$> substitute1Ast i var a
  Ast.AstFromDual a -> Ast.AstFromDual <$> substitute1Ast i var a

  Ast.AstSumOfList args ->
    let margs = NonEmpty.map (substitute1Ast i var) args
    in if any isJust margs
       then Just $ case isTensorInt v1 of
         Just Refl -> foldr1 contractAstPlusOp
                      $ NonEmpty.zipWith fromMaybe args margs
         _ -> astSumOfList $ NonEmpty.zipWith fromMaybe args margs
       else Nothing

  Ast.AstN1K opCode u ->
    (\u2 -> case isTensorInt u2 of
       Just Refl -> contractAstNumOp1 opCode u2
       _ -> Ast.AstN1K opCode u2)
    <$> substitute1Ast i var u
  Ast.AstN2K opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ case isTensorInt u of
         Just Refl -> contractAstNumOp2 opCode (fromMaybe u mu) (fromMaybe v mv)
         _ -> Ast.AstN2K opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstR1K opCode u -> Ast.AstR1K opCode <$> substitute1Ast i var u
  Ast.AstR2K opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstR2K opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstI2K opCode u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ case isTensorInt u of
         Just Refl ->
           contractAstIntegralOp2 opCode (fromMaybe u mu) (fromMaybe v mv)
         _ -> Ast.AstI2K opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstFloorK a -> Ast.AstFloorK <$> substitute1Ast i var a
  Ast.AstFromIntegralK v -> astFromIntegralK <$> substitute1Ast i var v
  Ast.AstCastK v -> astCastK <$> substitute1Ast i var v

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

  Ast.AstIndexS shn v ix ->
    case (substitute1Ast i var v, substitute1AstIxS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astIndexS shn (fromMaybe v mv) (fromMaybe ix mix)
  Ast.AstScatterS shn v (vars, ix) ->
    case (substitute1Ast i var v, substitute1AstIxS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astScatterS shn
                                      (fromMaybe v mv)
                                      (vars, fromMaybe ix mix)
  Ast.AstGatherS shn v (vars, ix) ->
    case (substitute1Ast i var v, substitute1AstIxS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astGatherS shn
                                     (fromMaybe v mv)
                                     (vars, fromMaybe ix mix)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS <$> substitute1Ast i var a
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS <$> substitute1Ast i var a
  Ast.AstIotaS{} -> Nothing
  Ast.AstAppendS x y ->
    case (substitute1Ast i var x, substitute1Ast i var y) of
      (Nothing, Nothing) -> Nothing
      (mx, my) -> Just $ astAppendS (fromMaybe x mx) (fromMaybe y my)
  Ast.AstSliceS i2 n k v -> astSliceS i2 n k <$> substitute1Ast i var v
  Ast.AstReverseS v -> astReverseS <$> substitute1Ast i var v
  Ast.AstTransposeS perm v -> astTransposeS perm <$> substitute1Ast i var v
  Ast.AstReshapeS sh v -> astReshapeS sh <$> substitute1Ast i var v
  Ast.AstZipS v -> Ast.AstZipS <$> substitute1Ast i var v
  Ast.AstUnzipS v -> Ast.AstUnzipS <$> substitute1Ast i var v
  Ast.AstNestS sh1 sh2 v ->
    astNestS sh1 sh2 <$> substitute1Ast i var v
  Ast.AstUnNestS v -> astUnNestS <$> substitute1Ast i var v

  Ast.AstFromS stkz v -> astFromS stkz <$> substitute1Ast i var v
  Ast.AstSFromK u -> astSFromK <$> substitute1Ast i var u
  Ast.AstSFromR sh v -> astSFromR sh <$> substitute1Ast i var v
  Ast.AstSFromX sh v -> astSFromX sh <$> substitute1Ast i var v

  Ast.AstReplicate0NS sh v -> Ast.AstReplicate0NS sh <$> substitute1Ast i var v
  Ast.AstSum0S v -> Ast.AstSum0S <$> substitute1Ast i var v
  Ast.AstDot0S u v ->
    let mu = substitute1Ast i var u
        mv = substitute1Ast i var v
    in if isJust mu || isJust mv
       then Just $ Ast.AstDot0S (fromMaybe u mu) (fromMaybe v mv)
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

substitute1AstIxS
  :: AstSpan s2
  => AstTensor AstMethodLet s2 y -> AstVarName s2 y -> AstIxS AstMethodLet sh
  -> Maybe (AstIxS AstMethodLet sh)
substitute1AstIxS i var ix =
  let mix = fmap (substitute1Ast i var) ix
  in if any isJust mix
     then Just $ zipWith_IndexS fromMaybe ix mix
     else Nothing

substitute1AstHFun
  :: forall s2 x y z.
     AstTensor AstMethodLet s2 z -> AstVarName s2 z -> AstHFun x y
  -> Maybe (AstHFun x y)
substitute1AstHFun _i _var = \case
  Ast.AstLambda{} -> Nothing  -- no outside free variables

substitute1AstBool :: AstSpan s2
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
  Ast.AstRel opCodeRel arg1 arg2 ->
    let mr1 = substitute1Ast i var arg1
        mr2 = substitute1Ast i var arg2
    in if isJust mr1 || isJust mr2
       then case ftkToSTK (ftkAst arg1) of
         STKScalar ->
           Just $ contractRelOp opCodeRel (fromMaybe arg1 mr1)
                                          (fromMaybe arg2 mr2)
         _ -> Just $ Ast.AstRel opCodeRel (fromMaybe arg1 mr1)
                                          (fromMaybe arg2 mr2)
       else Nothing


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
