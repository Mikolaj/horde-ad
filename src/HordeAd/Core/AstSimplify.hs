{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | This module holds smart constructors for AST, that is,
-- term-simplifying combinators corresponding to the Ast constructors,
-- and a few complete bottom-up simplifying functions. The former
-- simplify only on the basis of inspecting the roots of their
-- argument term trees. If the arguments get modified,
-- the modified forms are again inspected and potentialy simplified again.
--
-- The limited simplification via combinators is enough to uncover redexes
-- for the vectorization rules to fire and to undo some of the complication
-- introduced by vectorization. The intention is to leave intact as much
-- as possible of the original terms provided by the user while making
-- sure subterms introduced by vectorization are maximally simplified.
module HordeAd.Core.AstSimplify
  ( -- * The simplifying combinators, one for almost each AST constructor
    astPair, astProject1, astProject2, astFromVector, astSum, astReplicate
  , astMapAccumRDer, astMapAccumLDer, astApply, astCond, astConcrete

  , astLet

  , astPrimalPart, astDualPart

  , astFloorK, astFromIntegralK, astCastK

  , astFloorS, astFromIntegralS, astCastS

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
    -- * Substitution operations
  , substituteAst, substituteAstIxS, substituteAstBool
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Control.Monad (mapAndUnzipM, mplus)
import Data.Foldable qualified as Foldable
import Data.Functor.Const
import Data.GADT.Compare
import Data.Int (Int64)
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
  , type (<=?)
  )
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (typeRep)
import Data.List (findIndex)

import Data.Array.Mixed.Lemmas
import Data.Array.Mixed.Permutation (DropLen, Perm (..), TakeLen, permInverse)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
import Data.Array.Mixed.Types (Init, Last, Tail, snatPlus, unsafeCoerceRefl)
import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Lemmas
import Data.Array.Nested.Internal.Shape
import Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Ast
  ( AstBool (AstBoolConst)
  , AstTensor ( AstConcreteK, AstConcreteS, AstPlusK, AstTimesK, AstPlusS
              , AstTimesS)
  )
import HordeAd.Core.Ast hiding (AstBool (..), AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersAst ()
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind
import HordeAd.Core.ConvertTensor

-- * Expressing operations as Gather; introduces new variable names

data RewritePhase =
  PhaseNone | PhaseSimplification | PhaseExpansion | PhaseContraction
 deriving Eq

data SimplifyKnobs = SimplifyKnobs
  { knobStepOnly :: Bool
  , knobPhase    :: RewritePhase
  }

defaultKnobs :: SimplifyKnobs
defaultKnobs = SimplifyKnobs False PhaseNone

-- | We keep AstTranspose terms for as long as possible, because
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
  let FTKS shn _ = ftkAst v
      shnPermuted = shsPermute perm (shsTakeLen perm shn)
  in funToVarsIxS @_ @AstMethodLet shnPermuted $ \ (!vars, !ix) ->
    -- See astGatherCase.AstTransposeS for similar code with more comments.
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
--
-- | This generates big terms that don't simplify well,
-- so we keep the AstReshape form until simplification gets stuck.
-- In fact, to simplify the terms we'd need advanced solving of equations
-- in integer arithmetic modulo. Moreover, when solving, we'd need to know
-- the range of all integer variables (taken from shapes) and the floor
-- and minimum/maximum terms (obtained by analysing the embedded Ast term),
-- because many of the emerging terms are not equal to their simplifed
-- forms without this data. Probably we could just subsitute @var `remH` range@
-- for each variable.
astReshapeAsGatherS
  :: forall sh sh2 r s. AstSpan s
  => SimplifyKnobs -> ShS sh2 -> AstTensor AstMethodLet s (TKS2 sh r)
  -> AstTensor AstMethodLet s (TKS2 sh2 r)
{-# NOINLINE astReshapeAsGatherS #-}
astReshapeAsGatherS knobs shOut v | Refl <- lemAppNil @sh2
                                  , Refl <- lemAppNil @sh
                                  , FTKS shIn _ <- ftkAst v =
  funToVarsIxS shOut $ \ (!vars, !ix) ->
    let fromInt :: Int -> AstInt AstMethodLet
        fromInt i = AstConcreteK (fromIntegral i)
        asts :: AstIxS AstMethodLet sh
        asts = let i :: AstInt AstMethodLet
                   i = toLinearIdxS @sh2 @'[] fromInt shOut ix
               in simplifyAstIxS $ fromLinearIdxS fromInt shIn i
                    -- we generate these, so we simplify
    in gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh) $
       gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[]) $
       astGatherKnobsS @sh2 @'[] @sh knobs ZSS v (vars, asts)


-- * The simplifying combinators, one for almost each AST constructor

astPair :: AstTensor AstMethodLet s x -> AstTensor AstMethodLet s y
        -> AstTensor AstMethodLet s (TKProduct x y)
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
  Ast.AstCond b v1 v2 -> astCond b (astProject1 v1) (astProject1 v2)
  Ast.AstLet var t v -> astLet var t (astProject1 v)
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
  Ast.AstCond b v1 v2 -> astCond b (astProject2 v1) (astProject2 v2)
  Ast.AstLet var t v -> astLet var t (astProject2 v)
  Ast.AstFromPrimal u1 -> Ast.AstFromPrimal $ astProject2 u1
  Ast.AstFromDual u1 -> Ast.AstFromDual $ astProject2 u1
  Ast.AstFromS (STKProduct _ stk2) u1 | FTKProduct{} <- ftkAst u1 ->
    astFromS stk2 $ astProject2 u1
  _ -> Ast.AstProject2 u

astFromVector :: forall y k s. AstSpan s
              => SNat k -> SingletonTK y
              -> Data.Vector.Vector (AstTensor AstMethodLet s y)
              -> AstTensor AstMethodLet s (BuildTensorKind k y)
astFromVector (SNat' @1) stk v = astReplicate (SNat @1) stk (v V.! 0)
astFromVector snat@SNat stk l = fromMaybe (Ast.AstFromVector snat stk l) $
  -- This disable some rules, e.g., indexing or summing of fromVector
  -- of concrete arrays, but allocating an extra array of the same size
  -- as the fromVector is not a big deal and early rules are better
  -- then the same rules in contraction phase.
  (case (sameAstSpan @s @PrimalSpan, stk) of
     (Just Refl, STKScalar) ->
       let unConc :: AstTensor AstMethodLet PrimalSpan y
                  -> Maybe (Concrete y)
           unConc (AstConcreteK a) = Just $ Concrete a
           unConc _ = Nothing
       in case V.mapM unConc l of
         Just l4 | V.null l4 -> error "astFromVector: empty vector"
         Just l4 -> Just $ astConcreteS (tfromVector snat stk l4)
         Nothing -> Nothing
     (Just Refl, STKS _ STKScalar) ->
       let unConc :: AstTensor AstMethodLet PrimalSpan y
                  -> Maybe (Concrete y)
           unConc (AstConcreteS a) = Just $ Concrete a
           unConc _ = Nothing
       in case V.mapM unConc l of
         Just l4 | V.null l4 -> error "astFromVector: empty vector"
         Just l4 -> Just $ astConcreteS (tfromVector snat stk l4)
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
  (let unFrom :: FullShapeTK x
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
       => SNat k -> SingletonTK y
       -> AstTensor AstMethodLet s (BuildTensorKind k y)
       -> AstTensor AstMethodLet s y
astSum snat@SNat stk t0 = case t0 of
  _ | Just Refl <- testEquality snat (SNat @0) ->
    let ftk = razeFTK snat stk (ftkAst t0)
    in fromPrimal $ astConcrete ftk (treplTarget 0 ftk)
  AstConcreteS @_ @sh2 t -> case stk of
    STKS @sh _ STKScalar ->
      gcastWith (unsafeCoerceRefl :: k ': sh :~: sh2) $
      astConcreteS (tsum snat stk $ Concrete t)
    STKScalar ->
      gcastWith (unsafeCoerceRefl :: '[k] :~: sh2) $
      astConcreteK (tsum snat stk $ Concrete t)
  Ast.AstIotaS (SNat @n) ->
    let i = fromInteger $ valueOf @n * (valueOf @n - 1) `div` 2
    in case stk of
      STKScalar -> AstConcreteK i
      STKS ZSS STKScalar -> AstConcreteS $ Nested.sscalar i
  Ast.AstReverseS v -> astSum snat stk v
  _ | Just Refl <- testEquality snat (SNat @1)
    , STKScalar <- stk ->
      astFromS STKScalar $ astIndexStepS ZSS t0 (0 :.$ ZIS)
  _ | Just Refl <- testEquality snat (SNat @1)
    , STKS sh _  <- stk ->  -- other cases too rare
      astIndexStepS sh t0 (0 :.$ ZIS)  -- astReshape slows down the CNNO test
  Ast.AstFromVector @y2 _ _ l ->
    gcastWith (unsafeCoerceRefl :: y2 :~: y) $
    case stk of
      STKScalar -> foldr1 (+) l
      STKR _ STKScalar -> foldr1 (+) l
      STKS _ STKScalar -> foldr1 (+) l
      STKX _ STKScalar -> foldr1 (+) l
      _ -> Ast.AstSum snat stk t0
  Ast.AstReplicate _ STKScalar v | STKScalar <- stk ->
    v * fromPrimal (AstConcreteK $ fromInteger $ fromSNat snat)
  Ast.AstReplicate _ _ v | STKR _ (STKScalar @r) <- stk ->
    case ftkAst v of
      FTKR sh' FTKScalar ->
        withCastRS sh' $ \(sh :: ShS sh) ->
          v * astFromS
                stk (fromPrimal $ AstConcreteS @r
                     $ Nested.sreplicateScal sh $ fromInteger $ fromSNat snat)
  Ast.AstReplicate _ _ v | STKX _ (STKScalar @r) <- stk ->
    case ftkAst v of
      FTKX sh' FTKScalar ->
        withCastXS sh' $ \(sh :: ShS sh) ->
          v * astFromS
                stk (fromPrimal $ AstConcreteS @r
                     $ Nested.sreplicateScal sh $ fromInteger $ fromSNat snat)
  Ast.AstReplicate _ STKS{} v | STKS sh (STKScalar @r) <- stk ->
          v * astFromS
                stk (fromPrimal $ AstConcreteS @r
                     $ Nested.sreplicateScal sh $ fromInteger $ fromSNat snat)
  -- Ast.AstLet var u v -> astLet var u (astSum snat v)
    -- this is problematic, because it keeps huge tensors alive for longer
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astSum snat stk v
  Ast.AstFromDual v -> Ast.AstFromDual $ astSum snat stk v
  {- TODO: this requires a check that the eliminated index is in bounds:
  Ast.AstScatterS @shm @shn @shp v (vars, _ :.$ ix)
    | STKS{} <- stk ->
      astScatterS @shm @shn @(Tail shp) v (vars, ix) -}
  Ast.AstFromS _ v -> case ftkToSTK (ftkAst v) of
    STKS (snat2 :$$ rest) x -> astFromS stk $ astSum snat2 (STKS rest x) v
    _ -> Ast.AstSum snat stk t0  -- products probably not worth the effort
  _ -> Ast.AstSum snat stk t0

astReplicate :: forall y k s. AstSpan s
             => SNat k -> SingletonTK y
             -> AstTensor AstMethodLet s y
             -> AstTensor AstMethodLet s (BuildTensorKind k y)
astReplicate snat@SNat stk = \case
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astReplicate snat stk v
  Ast.AstFromDual v -> Ast.AstFromDual $ astReplicate snat stk v
  {- This is a bad idea, because transpose should be pushed down, not pulled up.
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
        fromMaybe (error "astReplicate: impossible non-permutation")
        $ Permutation.permCheckPermutation zsuccPerm
        $ astTransposeS zsuccPerm $ astReplicate snat (ftkToSTK (ftkAst v)) v -}
  -- This is a bad idea, because reshape should be pushed down, not pulled up.
  -- Ast.AstReshape sh v ->
  --  AstReshape (k :$: sh) $ astReplicate k v
  Ast.AstFromS stkz v ->
    astFromS (buildSTK snat stkz) $ astReplicate snat (ftkToSTK (ftkAst v)) v
  v -> Ast.AstReplicate snat stk v

-- TODO: also push up AstFromPrimal, etc.
astMapAccumRDer
  :: forall accy by ey k s. AstSpan s
  => SNat k
  -> FullShapeTK by
  -> FullShapeTK ey
  -> AstHFun s s
             (TKProduct accy ey) (TKProduct accy by)
  -> AstHFun s s
             (TKProduct (ADTensorKind (TKProduct accy ey))
                        (TKProduct accy ey))
             (ADTensorKind (TKProduct accy by))
  -> AstHFun s s
             (TKProduct (ADTensorKind (TKProduct accy by))
                        (TKProduct accy ey))
             (ADTensorKind (TKProduct accy ey))
  -> AstTensor AstMethodLet s accy
  -> AstTensor AstMethodLet s (BuildTensorKind k ey)
  -> AstTensor AstMethodLet s (TKProduct accy (BuildTensorKind k by))
astMapAccumRDer k bftk eftk (AstLambda varf vf)
                            (AstLambda vard vd)
                            (AstLambda varr vr)
                (Ast.AstFromS @accyFrom accstk acc0From) es =
  let accftkFrom = ftkAst acc0From
      accFromSTK = ftkToSTK accftkFrom
      ftkf2 = FTKProduct accftkFrom eftk
      varf2 = mkAstVarName ftkf2 (varNameToBounds varf) (varNameToAstVarId varf)
      astf2 = Ast.AstVar varf2
      vf2 =
        let subbed =
              substituteAst
                (astPair (astFromS @accyFrom accstk (astProject1 astf2))
                         (astProject2 astf2))
                varf vf
        in astSFrom @(TKProduct accy by)
                    (STKProduct accFromSTK (ftkToSTK bftk))
                    subbed
      ftkd2 = FTKProduct
                (adFTK $ FTKProduct accftkFrom eftk)
                (FTKProduct accftkFrom eftk)
      vard2 = mkAstVarName ftkd2 (varNameToBounds vard) (varNameToAstVarId vard)
      astd2 = Ast.AstVar vard2
      vd2 =
        let subbed =
              substituteAst
                (astPair (astPair (astFromS @(ADTensorKind accyFrom)
                                     (adSTK accstk)
                                     (astProject1 (astProject1 astd2)))
                                  (astProject2 (astProject1 astd2)))
                         (astPair (astFromS @accyFrom accstk
                                     (astProject1 (astProject2 astd2)))
                                  (astProject2 (astProject2 astd2))))
                vard vd
        in astSFrom @(ADTensorKind (TKProduct accy by))
                    (adSTK $ STKProduct accFromSTK (ftkToSTK bftk))
                    subbed
      ftkr2 = FTKProduct
                (adFTK $ FTKProduct accftkFrom bftk)
                (FTKProduct accftkFrom eftk)
      varr2 = mkAstVarName ftkr2 (varNameToBounds varr) (varNameToAstVarId varr)
      astr2 = Ast.AstVar varr2
      vr2 =
        let subbed =
              substituteAst
                (astPair (astPair (astFromS @(ADTensorKind accyFrom)
                                     (adSTK accstk)
                                     (astProject1 (astProject1 astr2)))
                                  (astProject2 (astProject1 astr2)))
                         (astPair (astFromS @accyFrom accstk
                                     (astProject1 (astProject2 astr2)))
                                  (astProject2 (astProject2 astr2))))
                varr vr
        in astSFrom @(ADTensorKind (TKProduct accy ey))
                    (adSTK $ STKProduct accFromSTK (ftkToSTK eftk))
                    subbed
  in astFromS @(TKProduct accyFrom (BuildTensorKind k by))
              (STKProduct accstk (buildSTK k (ftkToSTK bftk)))
     $ astMapAccumRDer k bftk eftk (AstLambda varf2 vf2)
                                   (AstLambda vard2 vd2)
                                   (AstLambda varr2 vr2)
                                   acc0From es
astMapAccumRDer k bftk eftk (AstLambda varf vf)
                            (AstLambda vard vd)
                            (AstLambda varr vr)
                acc0 (Ast.AstFromS @esShsFrom _esShsSTK esFrom) =
  let accftk = ftkAst acc0
      accstk = ftkToSTK accftk
      esShsFrom = ftkAst esFrom
      esShsFromSTK = ftkToSTK esShsFrom
  in case razeSTK esShsFromSTK of
    (eftkFromSTK :: SingletonTK eyFrom) ->
      gcastWith (unsafeCoerceRefl
                 :: BuildTensorKind k eyFrom :~: esShsFrom) $
      let eftkFrom = razeFTK k eftkFromSTK esShsFrom
          ftkf2 = FTKProduct accftk eftkFrom
          varf2 =
            mkAstVarName ftkf2 (varNameToBounds varf) (varNameToAstVarId varf)
          astf2 = Ast.AstVar varf2
          vf2 =
            let subbed =
                  substituteAst
                    (astPair (astProject1 astf2)
                             (astFromS @eyFrom
                                (ftkToSTK eftk) (astProject2 astf2)))
                    varf vf
            in subbed
          ftkd2 = FTKProduct
                    (adFTK $ FTKProduct accftk eftkFrom)
                    (FTKProduct accftk eftkFrom)
          vard2 =
            mkAstVarName ftkd2 (varNameToBounds vard) (varNameToAstVarId vard)
          astd2 = Ast.AstVar vard2
          vd2 =
            let subbed =
                  substituteAst
                    (astPair (astPair (astProject1 (astProject1 astd2))
                                      (astFromS @(ADTensorKind eyFrom)
                                         (adSTK (ftkToSTK eftk))
                                         (astProject2 (astProject1 astd2))))
                             (astPair (astProject1 (astProject2 astd2))
                                      (astFromS @eyFrom (ftkToSTK eftk)
                                         (astProject2 (astProject2 astd2)))))
                    vard vd
            in subbed
          ftkr2 = FTKProduct
                    (adFTK $ FTKProduct accftk bftk)
                    (FTKProduct accftk eftkFrom)
          varr2 =
            mkAstVarName ftkr2 (varNameToBounds varr) (varNameToAstVarId varr)
          astr2 = Ast.AstVar varr2
          vr2 =
            let subbed =
                  substituteAst
                    (astPair (astProject1 astr2)
                             (astPair (astProject1 (astProject2 astr2))
                                      (astFromS @eyFrom (ftkToSTK eftk)
                                         (astProject2 (astProject2 astr2)))))
                    varr vr
            in astSFrom @(ADTensorKind (TKProduct accy ey))
                        (adSTK $ STKProduct accstk eftkFromSTK)
                        subbed
      in astMapAccumRDer k bftk eftkFrom (AstLambda varf2 vf2)
                                         (AstLambda vard2 vd2)
                                         (AstLambda varr2 vr2)
                                         acc0 esFrom
astMapAccumRDer k bftk eftk f df rf acc0 es =
  Ast.AstMapAccumRDer k bftk eftk f df rf acc0 es

astMapAccumLDer
  :: forall accy by ey k s. AstSpan s
  => SNat k
  -> FullShapeTK by
  -> FullShapeTK ey
  -> AstHFun s s
             (TKProduct accy ey) (TKProduct accy by)
  -> AstHFun s s
             (TKProduct (ADTensorKind (TKProduct accy ey))
                        (TKProduct accy ey))
             (ADTensorKind (TKProduct accy by))
  -> AstHFun s s
             (TKProduct (ADTensorKind (TKProduct accy by))
                        (TKProduct accy ey))
             (ADTensorKind (TKProduct accy ey))
  -> AstTensor AstMethodLet s accy
  -> AstTensor AstMethodLet s (BuildTensorKind k ey)
  -> AstTensor AstMethodLet s (TKProduct accy (BuildTensorKind k by))
astMapAccumLDer k bftk eftk (AstLambda varf vf)
                            (AstLambda vard vd)
                            (AstLambda varr vr)
                (Ast.AstFromS @accyFrom accstk acc0From) es =
  let accftkFrom = ftkAst acc0From
      accFromSTK = ftkToSTK accftkFrom
      ftkf2 = FTKProduct accftkFrom eftk
      varf2 = mkAstVarName ftkf2 (varNameToBounds varf) (varNameToAstVarId varf)
      astf2 = Ast.AstVar varf2
      vf2 =
        let subbed =
              substituteAst
                (astPair (astFromS @accyFrom accstk (astProject1 astf2))
                         (astProject2 astf2))
                varf vf
        in astSFrom @(TKProduct accy by)
                    (STKProduct accFromSTK (ftkToSTK bftk))
                    subbed
      ftkd2 = FTKProduct
                (adFTK $ FTKProduct accftkFrom eftk)
                (FTKProduct accftkFrom eftk)
      vard2 = mkAstVarName ftkd2 (varNameToBounds vard) (varNameToAstVarId vard)
      astd2 = Ast.AstVar vard2
      vd2 =
        let subbed =
              substituteAst
                (astPair (astPair (astFromS @(ADTensorKind accyFrom)
                                     (adSTK accstk)
                                     (astProject1 (astProject1 astd2)))
                                  (astProject2 (astProject1 astd2)))
                         (astPair (astFromS @accyFrom accstk
                                     (astProject1 (astProject2 astd2)))
                                  (astProject2 (astProject2 astd2))))
                vard vd
        in astSFrom @(ADTensorKind (TKProduct accy by))
                    (adSTK $ STKProduct accFromSTK (ftkToSTK bftk))
                    subbed
      ftkr2 = FTKProduct
                (adFTK $ FTKProduct accftkFrom bftk)
                (FTKProduct accftkFrom eftk)
      varr2 = mkAstVarName ftkr2 (varNameToBounds varr) (varNameToAstVarId varr)
      astr2 = Ast.AstVar varr2
      vr2 =
        let subbed =
              substituteAst
                (astPair (astPair (astFromS @(ADTensorKind accyFrom)
                                     (adSTK accstk)
                                     (astProject1 (astProject1 astr2)))
                                  (astProject2 (astProject1 astr2)))
                         (astPair (astFromS @accyFrom accstk
                                     (astProject1 (astProject2 astr2)))
                                  (astProject2 (astProject2 astr2))))
                varr vr
        in astSFrom @(ADTensorKind (TKProduct accy ey))
                    (adSTK $ STKProduct accFromSTK (ftkToSTK eftk))
                    subbed
  in astFromS @(TKProduct accyFrom (BuildTensorKind k by))
              (STKProduct accstk (buildSTK k (ftkToSTK bftk)))
     $ astMapAccumLDer k bftk eftk (AstLambda varf2 vf2)
                                   (AstLambda vard2 vd2)
                                   (AstLambda varr2 vr2)
                                   acc0From es
astMapAccumLDer k bftk eftk (AstLambda varf vf)
                            (AstLambda vard vd)
                            (AstLambda varr vr)
                acc0 (Ast.AstFromS @esShsFrom _esShsSTK esFrom) =
  let accftk = ftkAst acc0
      accstk = ftkToSTK accftk
      esShsFrom = ftkAst esFrom
      esShsFromSTK = ftkToSTK esShsFrom
  in case razeSTK esShsFromSTK of
    (eftkFromSTK :: SingletonTK eyFrom) ->
      gcastWith (unsafeCoerceRefl
                 :: BuildTensorKind k eyFrom :~: esShsFrom) $
      let eftkFrom = razeFTK k eftkFromSTK esShsFrom
          ftkf2 = FTKProduct accftk eftkFrom
          varf2 =
            mkAstVarName ftkf2 (varNameToBounds varf) (varNameToAstVarId varf)
          astf2 = Ast.AstVar varf2
          vf2 =
            let subbed =
                  substituteAst
                    (astPair (astProject1 astf2)
                             (astFromS @eyFrom
                                (ftkToSTK eftk) (astProject2 astf2)))
                    varf vf
            in subbed
          ftkd2 = FTKProduct
                    (adFTK $ FTKProduct accftk eftkFrom)
                    (FTKProduct accftk eftkFrom)
          vard2 =
            mkAstVarName ftkd2 (varNameToBounds vard) (varNameToAstVarId vard)
          astd2 = Ast.AstVar vard2
          vd2 =
            let subbed =
                  substituteAst
                    (astPair (astPair (astProject1 (astProject1 astd2))
                                      (astFromS @(ADTensorKind eyFrom)
                                         (adSTK (ftkToSTK eftk))
                                         (astProject2 (astProject1 astd2))))
                             (astPair (astProject1 (astProject2 astd2))
                                      (astFromS @eyFrom (ftkToSTK eftk)
                                         (astProject2 (astProject2 astd2)))))
                    vard vd
            in subbed
          ftkr2 = FTKProduct
                    (adFTK $ FTKProduct accftk bftk)
                    (FTKProduct accftk eftkFrom)
          varr2 =
            mkAstVarName ftkr2 (varNameToBounds varr) (varNameToAstVarId varr)
          astr2 = Ast.AstVar varr2
          vr2 =
            let subbed =
                  substituteAst
                    (astPair (astProject1 astr2)
                             (astPair (astProject1 (astProject2 astr2))
                                      (astFromS @eyFrom (ftkToSTK eftk)
                                         (astProject2 (astProject2 astr2)))))
                    varr vr
            in astSFrom @(ADTensorKind (TKProduct accy ey))
                        (adSTK $ STKProduct accstk eftkFromSTK)
                        subbed
      in astMapAccumLDer k bftk eftkFrom (AstLambda varf2 vf2)
                                         (AstLambda vard2 vd2)
                                         (AstLambda varr2 vr2)
                                         acc0 esFrom
astMapAccumLDer k bftk eftk f df rf acc0 es =
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es

astApply :: forall x z s1 s. (AstSpan s1, AstSpan s)
         => AstHFun s1 s x z -> AstTensor AstMethodLet s1 x
         -> AstTensor AstMethodLet s z
astApply (AstLambda !var !v) u = astLet var u v

astCond :: AstSpan s
        => AstBool AstMethodLet
        -> AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
        -> AstTensor AstMethodLet s y
astCond (AstBoolConst b) v w = if b then v else w
astCond (Ast.AstBoolNot b) v w = astCond b w v
astCond b (Ast.AstFromPrimal v) (Ast.AstFromPrimal w) =
  Ast.AstFromPrimal $ astCond b v w
astCond b (Ast.AstFromDual v) (Ast.AstFromDual w) =
  Ast.AstFromDual $ astCond b v w
astCond b v@(Ast.AstFromS STKScalar _) w = Ast.AstCond b v w
astCond b (Ast.AstFromS stkzv v) (Ast.AstFromS _ w) =
  case matchingFTK (ftkAst v) (ftkAst w) of
    Just Refl -> astFromS stkzv $ astCond b v w
    Nothing -> error "astCond: shapes don't match"
astCond b v w = Ast.AstCond b v w

astLet :: forall y z s s2. (AstSpan s, AstSpan s2)
       => AstVarName s y -> AstTensor AstMethodLet s y
       -> AstTensor AstMethodLet s2 z
       -> AstTensor AstMethodLet s2 z
astLet _var _u v@Ast.AstConcreteK{} = v
astLet _var _u v@Ast.AstConcreteS{} = v
astLet _var _u v@Ast.AstIotaS{} = v
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
      substituteAst (Ast.AstPair ast1 ast2) var v
astLet var (Ast.AstFromPrimal (Ast.AstLet varN uN (Ast.AstPair u1 u2))) v =
  astLet varN uN
  $ astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
      substituteAst (Ast.AstFromPrimal (Ast.AstPair ast1 ast2)) var v
astLet var (Ast.AstFromDual (Ast.AstLet varN uN (Ast.AstPair u1 u2))) v =
  astLet varN uN
  $ astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
      substituteAst (Ast.AstFromDual (Ast.AstPair ast1 ast2)) var v
-- This is a common case, e.g., from representing conditionals.
astLet var (Ast.AstFromVector snat stk u) v | V.length u == 2 =
  astLetFun (u V.! 0) $ \ !ast1 -> astLetFun (u V.! 1) $ \ !ast2 ->
    substituteAst (Ast.AstFromVector snat stk $ fromList [ast1, ast2]) var v
astLet var (Ast.AstFromPrimal
              (Ast.AstFromVector snat stk u)) v | V.length u == 2 =
  astLetFun (u V.! 0) $ \ !ast1 -> astLetFun (u V.! 1) $ \ !ast2 ->
    substituteAst (Ast.AstFromPrimal (Ast.AstFromVector snat stk
                                      $ fromList [ast1, ast2])) var v
astLet var (Ast.AstFromDual
              (Ast.AstFromVector snat stk u)) v | V.length u == 2 =
  astLetFun (u V.! 0) $ \ !ast1 -> astLetFun (u V.! 1) $ \ !ast2 ->
    substituteAst (Ast.AstFromDual (Ast.AstFromVector snat stk
                                    $ fromList [ast1, ast2])) var v
astLet var (Ast.AstLet varN uN
              (Ast.AstFromVector snat stk u)) v | V.length u == 2 =
  astLet varN uN
  $ astLetFun (u V.! 0) $ \ !ast1 -> astLetFun (u V.! 1) $ \ !ast2 ->
      substituteAst (Ast.AstFromVector snat stk $ fromList [ast1, ast2]) var v
astLet var (Ast.AstFromPrimal
              (Ast.AstLet varN uN
                 (Ast.AstFromVector snat stk u))) v | V.length u == 2 =
  astLet varN uN
  $ astLetFun (u V.! 0) $ \ !ast1 -> astLetFun (u V.! 1) $ \ !ast2 ->
      substituteAst (Ast.AstFromPrimal (Ast.AstFromVector snat stk
                                        $ fromList [ast1, ast2])) var v
astLet var (Ast.AstFromDual
              (Ast.AstLet varN uN
                 (Ast.AstFromVector snat stk u))) v | V.length u == 2 =
  astLet varN uN
  $ astLetFun (u V.! 0) $ \ !ast1 -> astLetFun (u V.! 1) $ \ !ast2 ->
      substituteAst (Ast.AstFromDual (Ast.AstFromVector snat stk
                                      $ fromList [ast1, ast2])) var v
astLet var u v@(Ast.AstVar var2) =
  if varNameToAstVarId var2 == varNameToAstVarId var
  then case sameAstSpan @s @s2 of
    Just Refl -> case testEquality var var2 of
      Just Refl -> u
      _ -> error "astLet: wrong variable types at AstVar"
    _ -> error "astLet: wrong span at AstVar"
  else v
astLet var u v@(Ast.AstPrimalPart (Ast.AstVar var2)) =  -- a common noop
  if varNameToAstVarId var2 == varNameToAstVarId var
  then case sameAstSpan @s @FullSpan of
    Just Refl -> case testEquality var var2 of
      Just Refl -> astPrimalPart u
      _ -> error "astLet: wrong variable types at AstPrimalPart"
    _ -> error "astLet: wrong span at AstPrimalPart"
  else v
astLet var u v@(Ast.AstDualPart (Ast.AstVar var2)) =  -- a noop
  if varNameToAstVarId var2 == varNameToAstVarId var
  then case sameAstSpan @s @FullSpan of
    Just Refl -> case testEquality var var2 of
      Just Refl -> astDualPart u
      _ -> error "astLet: wrong variable types at AstDualPart"
    _ -> error "astLet: wrong span at AstDualPart"
  else v
astLet var u (Ast.AstFromPrimal v0) = Ast.AstFromPrimal $ astLet var u v0
astLet var u (Ast.AstFromDual v0) = Ast.AstFromDual $ astLet var u v0
astLet var u (Ast.AstFromS stkz v) =
  astFromS stkz $ astLet var u v
astLet var (Ast.AstFromS stkz a) v =
  let var2 =
        mkAstVarName (ftkAst a) (varNameToBounds var) (varNameToAstVarId var)
      ast = astFromS stkz $ Ast.AstVar var2
  in astLet var2 a (substituteAst ast var v)
astLet var u v = Ast.AstLet var u v

-- | A special variant to bind integer expressions inside indexes.
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
  {- Ast.AstMapAccumRDer k bftk eftk (AstLambda varf vf)
                                  (AstLambda vard vd)
                                  (AstLambda varr vr) acc0 es ->
    astMapAccumRDer k bftk eftk f df rf
                    (astPrimalPart acc0) (astPrimalPart es)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    astMapAccumLDer k bftk eftk f df rf
                    (astPrimalPart acc0) (astPrimalPart es) -}
  Ast.AstMapAccumRDer{} -> Ast.AstPrimalPart t  -- TODO
  Ast.AstMapAccumLDer{} -> Ast.AstPrimalPart t
  Ast.AstApply (AstLambda !var !v) ll ->
    astApply (AstLambda var (astPrimalPart v)) ll
  Ast.AstVar{} -> Ast.AstPrimalPart t  -- the only normal form
  Ast.AstCond b a2 a3 -> astCond b (astPrimalPart a2) (astPrimalPart a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = astPrimalPart v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var u (astPrimalPart v)

  Ast.AstFromPrimal v -> v
  Ast.AstFromDual v ->
    let ftk = ftkAst v
    in astConcrete ftk (treplTarget 0 ftk)

  AstPlusK u v -> astPrimalPart u + astPrimalPart v
  AstTimesK u v -> astPrimalPart u * astPrimalPart v
  Ast.AstN1K NegateOp u -> negate (astPrimalPart u)
  Ast.AstN1K AbsOp u -> abs (astPrimalPart u)
  Ast.AstN1K SignumOp u -> signum (astPrimalPart u)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (astPrimalPart u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2K QuotOp u v -> quotH (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2K RemOp u v -> remH (astPrimalPart u) (astPrimalPart v)
  Ast.AstCastK v -> astCastK $ astPrimalPart v

  AstPlusS u v -> astPrimalPart u + astPrimalPart v
  AstTimesS u v -> astPrimalPart u * astPrimalPart v
  Ast.AstN1S NegateOp u -> negate (astPrimalPart u)
  Ast.AstN1S AbsOp u -> abs (astPrimalPart u)
  Ast.AstN1S SignumOp u -> signum (astPrimalPart u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astPrimalPart u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (astPrimalPart u)
                                             (astPrimalPart v)
  Ast.AstI2S QuotOp u v -> quotH (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2S RemOp u v -> remH (astPrimalPart u) (astPrimalPart v)
  Ast.AstCastS v -> astCastS $ astPrimalPart v

  Ast.AstIndexS shn v ix ->
    astIndexStepS shn (astPrimalPart v) ix
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
  Ast.AstSum0S{} -> Ast.AstPrimalPart t
  Ast.AstDot0S{} -> Ast.AstPrimalPart t
  Ast.AstDot1InS{} -> Ast.AstPrimalPart t
  Ast.AstMatmul2S{} -> Ast.AstPrimalPart t

-- Note how this can't be pushed down into, say, multiplication, because it
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
  {- Ast.AstMapAccumRDer k bftk eftk f df rf acc0 es ->
    astMapAccumRDer k bftk eftk f df rf
                    (astDualPart acc0) (astDualPart es)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    astMapAccumLDer k bftk eftk f df rf
                    (astDualPart acc0) (astDualPart es) -}
  Ast.AstMapAccumRDer{} -> Ast.AstDualPart t  -- TODO
  Ast.AstMapAccumLDer{} -> Ast.AstDualPart t
  Ast.AstApply (AstLambda !var !v) ll ->
    astApply (AstLambda var (astDualPart v)) ll
  Ast.AstVar{} -> Ast.AstDualPart t
  Ast.AstCond b a2 a3 -> astCond b (astDualPart a2) (astDualPart a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = astDualPart v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var u (astDualPart v)

  Ast.AstFromPrimal v ->
    let ftk = ftkAst v
    in Ast.AstDualPart $ Ast.AstFromPrimal
       $ astConcrete ftk (treplTarget 0 ftk)
           -- let's hope this is smaller than v
  Ast.AstFromDual v -> v

  AstPlusK u v -> astDualPart u + astDualPart v
  -- This one is mathematically wrong, dual numbers don't mult like that:
  -- AstTimesK u v -> astDualPart u * astDualPart v
  Ast.AstN1K NegateOp u -> negate (astDualPart u)
  {- Some of these are wrong, so let's be conservative:
  Ast.AstN1K AbsOp u -> abs (astDualPart u)
  Ast.AstN1K SignumOp u -> signum (astDualPart u)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (astDualPart u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (astDualPart u) (astDualPart v)
  Ast.AstI2K QuotOp u v -> quotH (astDualPart u) (astDualPart v)
  Ast.AstI2K RemOp u v -> remH (astDualPart u) (astDualPart v)
  -}
  Ast.AstCastK v -> astCastK $ astDualPart v

  AstPlusS u v -> astDualPart u + astDualPart v
  -- This one is mathematically wrong, dual numbers don't mult like that:
  -- AstTimesS u v -> astDualPart u * astDualPart v
  Ast.AstN1S NegateOp u -> negate (astDualPart u)
  {- Some of these are wrong, so let's be conservative:
  Ast.AstN1S AbsOp u -> abs (astDualPart u)
  Ast.AstN1S SignumOp u -> signum (astDualPart u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astDualPart u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (astDualPart u)
                                             (astDualPart v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (astDualPart u)
                                             (astDualPart v)
  -}
  Ast.AstCastS v -> astCastS $ astDualPart v

  Ast.AstIndexS shn v ix ->
    astIndexStepS shn (astDualPart v) ix
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
  Ast.AstSum0S{} -> Ast.AstDualPart t
  Ast.AstDot0S{} -> Ast.AstDualPart t
  Ast.AstDot1InS{} -> Ast.AstDualPart t
  Ast.AstMatmul2S{} -> Ast.AstDualPart t

  _ -> Ast.AstDualPart t

astConcreteK :: GoodScalar r
             => Concrete (TKScalar r)
             -> AstTensor AstMethodLet PrimalSpan (TKScalar r)
astConcreteK = AstConcreteK . unConcrete

astFloorK :: (GoodScalar r1, RealFrac r1, GoodScalar r2, Integral r2)
          => AstTensor AstMethodLet PrimalSpan (TKScalar r1)
          -> AstTensor AstMethodLet PrimalSpan (TKScalar r2)
astFloorK t = case t of
  -- These values are small, so we can simplify then ASAP.
  AstConcreteK k -> astConcreteK (tkfloor $ Concrete k)
  Ast.AstFloorK v -> astFloorK v
  Ast.AstFromIntegralK v -> astFromIntegralK v
  Ast.AstCastK v -> astFloorK v
  _ -> Ast.AstFloorK t

-- Beware that increasing the number of calls to this constructor
-- sometimes increases runtime, because not enough copies cancel out.
-- Hence the commented out rules below.
astFromIntegralK :: forall r1 r2. (GoodScalar r1, GoodScalar r2, Integral r1)
                 => AstTensor AstMethodLet PrimalSpan (TKScalar r1)
                 -> AstTensor AstMethodLet PrimalSpan (TKScalar r2)
astFromIntegralK t = case t of
  _ | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) -> t
--  Ast.AstCond b a2 a3 ->
--    Ast.AstCond b (astFromIntegralK a2) (astFromIntegralK a3)
  AstConcreteK k -> astConcreteK (tkfromIntegral $ Concrete k)
  Ast.AstN1K NegateOp u -> negate (astFromIntegralK u)
  Ast.AstN1K AbsOp u -> abs (astFromIntegralK u)
  Ast.AstN1K SignumOp u -> signum (astFromIntegralK u)
  Ast.AstFromIntegralK v -> astFromIntegralK v
  _ -> Ast.AstFromIntegralK t

astCastK :: forall r1 r2 s.
            (GoodScalar r1, GoodScalar r2, RealFrac r1, RealFrac r2, AstSpan s)
         => AstTensor AstMethodLet s (TKScalar r1)
         -> AstTensor AstMethodLet s (TKScalar r2)
astCastK t = case t of
  _ | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) -> t
--  Ast.AstCond b a2 a3 -> Ast.AstCond b (astCastK a2) (astCastK a3)
  AstConcreteK k -> astConcreteK (tkcast $ Concrete k)
  -- TODO: which should go deeper, casts or fromPrimal? Or maybe alternate
  -- to make sure both can cancel out? Rethink. For now, astFromPrimal
  -- is not called to avoid loops. The same with many others
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astCastK v
  Ast.AstFromDual v -> Ast.AstFromDual $ astCastK v
  Ast.AstN1K NegateOp u -> negate (astCastK u)
  Ast.AstN1K AbsOp u -> abs (astCastK u)
  Ast.AstN1K SignumOp u -> signum (astCastK u)
--  Ast.AstR1K opCode u -> Ast.AstR1K opCode (astCastK u)
  Ast.AstFromIntegralK v -> astFromIntegralK v
  Ast.AstCastK v -> astCastK v
  _ -> Ast.AstCastK t

astConcreteS :: GoodScalar r
             => Concrete (TKS sh r)
             -> AstTensor AstMethodLet PrimalSpan (TKS sh r)
astConcreteS = AstConcreteS . unConcrete

astFloorS :: (GoodScalar r1, RealFrac r1, Integral r2, GoodScalar r2)
          => AstTensor AstMethodLet PrimalSpan (TKS sh r1)
          -> AstTensor AstMethodLet PrimalSpan (TKS sh r2)
astFloorS t = case t of
  Ast.AstReplicate snat (STKS sh STKScalar) a ->
    astReplicate snat (STKS sh STKScalar) (astFloorS a)
  Ast.AstReplicate snat STKScalar a ->
    astReplicate snat STKScalar (astFloorK a)
  Ast.AstBuild1 snat (STKS sh STKScalar) (var, v) ->
    Ast.AstBuild1 snat (STKS sh STKScalar) (var, astFloorS v)
  Ast.AstBuild1 snat STKScalar (var, v) ->
    Ast.AstBuild1 snat STKScalar (var, astFloorK v)
  Ast.AstLet var u v -> astLet var u (astFloorS v)
  Ast.AstScatterS shn v (vars, ix) ->
    astScatterS shn (astFloorS v) (vars, ix)
  Ast.AstGatherS shn v (vars, ix) ->
    astGatherS shn (astFloorS v) (vars, ix)
  Ast.AstIotaS snat -> Ast.AstIotaS snat
  Ast.AstReverseS v -> astReverseS (astFloorS v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astFloorS v)
  Ast.AstReshapeS sh v -> astReshapeS sh (astFloorS v)
  Ast.AstSFromK v -> astSFromK (astFloorK v)
  Ast.AstFloorS v -> astFloorS v
  Ast.AstFromIntegralS v -> astFromIntegralS v
  Ast.AstCastS v -> astFloorS v
  _ -> Ast.AstFloorS t

astFromIntegralS :: forall r1 r2 sh. (GoodScalar r1, GoodScalar r2, Integral r1)
                 => AstTensor AstMethodLet PrimalSpan (TKS sh r1)
                 -> AstTensor AstMethodLet PrimalSpan (TKS sh r2)
astFromIntegralS t = case t of
  _ | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) -> t
--  Ast.AstFromVector snat (STKS sh STKScalar) l ->
--   astFromVector snat (STKS sh STKScalar) (V.map astFromIntegralS l)
--  Ast.AstFromVector snat STKScalar l ->
--   astFromVector snat STKScalar (V.map astFromIntegralK l)
  Ast.AstReplicate snat (STKS sh STKScalar) a ->
    astReplicate snat (STKS sh STKScalar) (astFromIntegralS a)
  Ast.AstReplicate snat STKScalar a ->
    astReplicate snat STKScalar (astFromIntegralK a)
--  Ast.AstCond b v w -> astCond b (astFromIntegralS v) (astFromIntegralS w)
  Ast.AstBuild1 snat (STKS sh STKScalar) (var, v) ->
    Ast.AstBuild1 snat (STKS sh STKScalar) (var, astFromIntegralS v)
  Ast.AstBuild1 snat STKScalar (var, v) ->
    Ast.AstBuild1 snat STKScalar (var, astFromIntegralK v)
  Ast.AstLet var u v -> astLet var u (astFromIntegralS v)
  Ast.AstN1S NegateOp u -> negate (astFromIntegralS u)
  Ast.AstN1S AbsOp u -> abs (astFromIntegralS u)
  Ast.AstN1S SignumOp u -> signum (astFromIntegralS u)
  Ast.AstFromIntegralS v -> astFromIntegralS v
--  Ast.AstIndexS shn v ix -> astIndexS shn (astFromIntegralS v) ix
    -- increases work; also index goes into fromIntegral, so we'd loop
  Ast.AstScatterS shn v (vars, ix) ->
    astScatterS shn (astFromIntegralS v) (vars, ix)
  Ast.AstGatherS shn v (vars, ix) ->
    astGatherS shn (astFromIntegralS v) (vars, ix)
  Ast.AstIotaS snat -> Ast.AstIotaS snat
--  Ast.AstSliceS i n k v -> astSliceS i n k (astFromIntegralS v)
  Ast.AstReverseS v -> astReverseS (astFromIntegralS v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astFromIntegralS v)
  Ast.AstReshapeS sh v -> astReshapeS sh (astFromIntegralS v)
  Ast.AstSFromK v -> astSFromK (astFromIntegralK v)
  _ -> Ast.AstFromIntegralS t

astCastS :: forall r1 r2 s sh.
            (GoodScalar r1, GoodScalar r2, RealFrac r1, RealFrac r2, AstSpan s)
         => AstTensor AstMethodLet s (TKS sh r1)
         -> AstTensor AstMethodLet s (TKS sh r2)
astCastS t = case t of
  _ | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) -> t
--  Ast.AstFromVector snat (STKS sh STKScalar) l ->
--   astFromVector snat (STKS sh STKScalar) (V.map astCastS l)
--  Ast.AstFromVector snat STKScalar l ->
--   astFromVector snat STKScalar (V.map astCastK l)
  {- This (and other similar rules) is bad, because it changes semantics
     and also impacts performance negatively (a is larger than sum a):
  Ast.AstSum snat (STKS sh STKScalar) a ->
    astSum snat (STKS sh STKScalar) (astCastS a) -}
  Ast.AstReplicate snat (STKS sh STKScalar) a ->
    astReplicate snat (STKS sh STKScalar) (astCastS a)
  Ast.AstReplicate snat STKScalar a ->
    astReplicate snat STKScalar (astCastK a)
--  Ast.AstCond b v w -> astCond b (astCastS v) (astCastS w)
  Ast.AstBuild1 snat (STKS sh STKScalar) (var, v) ->
    Ast.AstBuild1 snat (STKS sh STKScalar) (var, astCastS v)
  Ast.AstBuild1 snat STKScalar (var, v) ->
    Ast.AstBuild1 snat STKScalar (var, astCastK v)
  Ast.AstLet var u v -> astLet var u (astCastS v)
  Ast.AstPrimalPart a -> Ast.AstPrimalPart $ astCastS a
  Ast.AstDualPart a -> Ast.AstDualPart $ astCastS a
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astCastS v
  Ast.AstFromDual v -> Ast.AstFromDual $ astCastS v
  Ast.AstN1S NegateOp u -> negate (astCastS u)
  Ast.AstN1S AbsOp u -> abs (astCastS u)
  Ast.AstN1S SignumOp u -> signum (astCastS u)
  Ast.AstFromIntegralS v -> astFromIntegralS v
  Ast.AstCastS v -> astCastS v
--  Ast.AstIndexS shn v ix -> astIndexS shn (astCastS v) ix
    -- increases work; also index goes into fromIntegral, so we'd loop
  Ast.AstScatterS shn v (vars, ix) -> astScatterS shn (astCastS v) (vars, ix)
  Ast.AstGatherS shn v (vars, ix) -> astGatherS shn (astCastS v) (vars, ix)
--  Ast.AstMinIndexS v -> Ast.AstMinIndexS (astCastS v)
  Ast.AstIotaS snat -> Ast.AstIotaS snat
--  Ast.AstSliceS i n k v -> astSliceS i n k (astCastS v)
  Ast.AstReverseS v -> astReverseS (astCastS v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astCastS v)
  Ast.AstReshapeS sh v -> astReshapeS sh (astCastS v)
  Ast.AstSFromK v -> astSFromK (astCastK v)
  _ -> Ast.AstCastS t

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
astIndexKnobsS _ shn v0 (AstConcreteK it :.$ _)
  | let i = fromIntegral it
        FTKS (snat :$$ _) x = ftkAst v0
  , not (0 <= i && i < sNatValue snat) =
    let ftk = FTKS shn x
    in fromPrimal $ astConcrete ftk (tdefTarget ftk)
astIndexKnobsS knobs shn v0 (Ast.AstCond b i1 i2 :.$ rest0)
  | knobPhase knobs /= PhaseNone =  -- don't undo what vectorization is doing
    astLetFun v0 $ \v ->
    shareIx rest0 $ \rest ->
      Ast.AstCond b (Ast.AstIndexS shn v (i1 :.$ rest))
                    (Ast.AstIndexS shn v (i2 :.$ rest))
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
  Ast.AstFromVector _ STKS{} l | AstConcreteK it <- i1 ->
    let i = fromIntegral it
    in astIndex shn (l V.! i) rest1
  Ast.AstFromVector _ STKScalar l | AstConcreteK it <- i1 ->
    let i = fromIntegral it
    in astIndex shn (astSFromK (l V.! i)) rest1
  Ast.AstFromVector{} | ZIS <- rest1 ->  -- normal form
    Ast.AstIndexS shn v0 ix
  Ast.AstFromVector snat STKS{} l ->
    shareIx rest1 $ \ !ix2 ->
      Ast.AstIndexS @'[in1] @shn shn (astFromVector snat (STKS shn (ftkToSTK x))
                                      $ V.map (\a -> astIndexRec shn a ix2) l)
                    (i1 :.$ ZIS)
  Ast.AstSum snat@(SNat @n1) STKS{} v ->
    let perm3 = backpermCycle $ shsLength (ixsToShS ix) + 1
    in Permutation.permFromList perm3 $ \(perm :: Permutation.Perm perm3P) ->
         gcastWith (unsafeCoerceRefl
                    :: Compare (Rank perm3P) (Rank (n1 : shm ++ shn))
                       :~: LT) $
         gcastWith (unsafeCoerceRefl
                    :: Permutation.PermutePrefix perm3P (n1 : (shm ++ shn))
                       :~: shm ++ (n1 : shn)) $
         fromMaybe (error "astIndexKnobsS: impossible non-permutation")
         $ Permutation.permCheckPermutation perm
         $ astSum snat (STKS shn (ftkToSTK x))
         $ astIndex @shm @(n1 : shn) (snat :$$ shn)
                    (astTransposeS @perm3P @(n1 : shm ++ shn) perm v)
                    ix
{- TODO: this slows down test 3nestedSumBuild1 orders of magnitude:
  Ast.AstReplicate k v ->
    let len = astConcrete $ fromIntegral k
        zero = astReplicate0N (dropShape $ shapeAst v) 0
    in case simplifyAstBool $ Ast.AstB2 AndOp (Ast.AstLeq 0 i1)
                                              (Ast.AstLeq i1 len) of
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
    STKS{} -> astIndex shn (astLet var2 i1 v) rest1
    STKScalar | ZIS <- rest1 -> astSFromK $ astLet var2 i1 v

  Ast.AstLet var u v -> astLet var u (astIndexRec shn v ix)

  Ast.AstPrimalPart{} -> Ast.AstIndexS shn v0 ix  -- must be a NF
  Ast.AstDualPart{} -> Ast.AstIndexS shn v0 ix
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astIndex shn v ix
  Ast.AstFromDual v -> Ast.AstFromDual $ astIndex shn v ix

  AstPlusS u v ->
    shareIx ix $ \ !ix2 ->
    astIndexRec shn u ix2 + astIndexRec shn v ix2
  AstTimesS u v ->
    shareIx ix $ \ !ix2 ->
    astIndexRec shn u ix2 * astIndexRec shn v ix2
  Ast.AstN1S NegateOp u -> negate (astIndexRec shn u ix)
  Ast.AstN1S AbsOp u -> abs (astIndexRec shn u ix)
  Ast.AstN1S SignumOp u -> signum (astIndexRec shn u ix)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astIndexRec shn u ix)
  Ast.AstR2S opCode u v ->
    shareIx ix
    $ \ !ix2 -> Ast.AstR2S opCode (astIndexRec shn u ix2)
                                  (astIndexRec shn v ix2)
  Ast.AstI2S opCode u v ->
    shareIx ix
    $ \ !ix2 -> Ast.AstI2S opCode (astIndexRec shn u ix2)
                                  (astIndexRec shn v ix2)
  AstConcreteS a ->
    let unConc :: AstInt AstMethodLet -> Maybe [IntOf Concrete]
               -> Maybe [IntOf Concrete]
        unConc (AstConcreteK i) (Just l) = Just $ Concrete i : l
        unConc _ _ = Nothing
    in case foldr unConc (Just []) ix of
      Just ixInt -> withKnownSTK (ftkToSTK x) $
                    withKnownShS shn $
                    withKnownShS (ixsToShS ix) $
                    astConcreteS (tsindex @_ @shm (Concrete a) (fromList ixInt))
      Nothing -> Ast.AstIndexS shn v0 ix
  Ast.AstFloorS v -> astFloorS $ astIndexKnobsS knobs shn v ix
  Ast.AstFromIntegralS v -> astFromIntegralS $ astIndexKnobsS knobs shn v ix
  Ast.AstCastS t -> astCastS $ astIndexKnobsS knobs shn t ix

  Ast.AstIndexS _ v (ix2 :: AstIxS AstMethodLet sh4)
    | Refl <- lemAppAssoc (Proxy @sh4) (Proxy @shm) (Proxy @shn) ->
      astIndex shn v (ix2 `ixsAppend` ix)
  Ast.AstScatterS @shm7 @shn7 @shp7 shn7 v (vars, AstIntVar var5 :.$ ix2)
    | AstIntVar var6 <- i1, var6 == var5 ->
        astIndex shn (astScatterS @shm7 @shn7 @(Tail shp7)
                                  shn7 v (vars, ix2)) rest1
  Ast.AstScatterS @shm7 @shn7 @shp7 shn7
                  v (vars, AstConcreteK i5 :.$ ix2)
    | AstConcreteK i6 <- i1 ->
        if i6 == i5
        then astIndex shn (astScatterS @shm7 @shn7 @(Tail shp7)
                                       shn7 v (vars, ix2)) rest1
        else let ftk = FTKS shn x
             in fromPrimal $ astConcrete ftk (treplTarget 0 ftk)
  -- AstScatter sh v (vars2, ZIR) ->
  --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZIR)
  Ast.AstScatterS{} ->  -- normal form
    Ast.AstIndexS shn v0 ix
  -- This is not a possible normal form, but pattern needs to be exhaustive.
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
      in astLet var2 i1 $ astIndex @shm1 @shn shn w rest1
  Ast.AstMinIndexS @n1 @shz v -> case ftkAst v of
    FTKS nsh _ -> case shsLast nsh of
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
  Ast.AstMaxIndexS @n1 @shz v -> case ftkAst v of
    FTKS nsh _ -> case shsLast nsh of
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
  Ast.AstIotaS{} -> case testEquality shn ZSS of
    Just Refl -> astFromIntegralS $ astSFromK i1
    _ -> error "astIndexKnobsS: shape not []"
  Ast.AstAppendS u v | FTKS (SNat @m :$$ _) _ <- ftkAst u ->
    let ulen = AstConcreteK (valueOf @m)
        ix1 = i1 :.$ rest1
        ix2 = simplifyAstInt (i1 - ulen) :.$ rest1
    in case simplifyAstBool $ AstLeqInt ulen i1 of
      AstBoolConst b -> if b then astIndex shn v ix2 else astIndex shn u ix1
      bExpr -> astCond bExpr (astIndexRec shn v ix2) (astIndexRec shn u ix1)
  Ast.AstSliceS (SNat @i) _ SNat v ->
    let ii = simplifyAstInt (fromIntegral (valueOf @i :: Int) + i1)
      -- we generate this index, so we simplify on the spot
    in astIndex shn v (ii :.$ rest1)
  Ast.AstReverseS v ->
    let iRev = simplifyAstInt (fromIntegral (valueOf @in1 - 1 :: Int) - i1)
      -- we generate this index, so we simplify on the spot
    in astIndex shn v (iRev :.$ rest1)
  Ast.AstTransposeS @_ @sh2 perm v
    | gcompare (shsRank (ixsToShS ix)) (Permutation.permRank perm) /= GLT ->
      -- TODO: remake once there's an S version of permInverse:
      permInverse perm $ \(permR :: Permutation.Perm permR) _ ->
      let ix2 :: AstIxS AstMethodLet (Permutation.PermutePrefix permR shm)
          ix2 = ixsPermutePrefix permR ix
      in gcastWith (unsafeCoerceRefl
                    :: sh2 :~: Permutation.PermutePrefix permR shm ++ shn) $
         astIndex @(Permutation.PermutePrefix permR shm) shn v ix2
  Ast.AstTransposeS{} | not (knobStepOnly knobs)
                        && knobPhase knobs /= PhaseExpansion ->
    Ast.AstIndexS shn v0 ix
  Ast.AstTransposeS @perm perm v ->
    astIndex shn (astTransposeAsGatherS @perm knobs perm v) ix
  Ast.AstReshapeS{} | not (knobStepOnly knobs)
                      && knobPhase knobs /= PhaseExpansion ->
    Ast.AstIndexS shn v0 ix
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
  Ast.AstDot1InS{} -> Ast.AstIndexS shn v0 ix
  Ast.AstMatmul2S{} -> Ast.AstIndexS shn v0 ix

-- TODO: compared to tletIx, it adds many lets, not one, but does not
-- create other (and non-simplified!) big terms and also uses astIsSmall,
-- so it's probably more efficient. Use this instead of tletIx
-- or design something even better.
shareIx :: AstSpan s
        => AstIxS AstMethodLet shm
        -> (AstIxS AstMethodLet shm -> AstTensor AstMethodLet s y)
        -> AstTensor AstMethodLet s y
{-# NOINLINE shareIx #-}
shareIx ix f = unsafePerformIO $ do
  let shareI :: (AstInt AstMethodLet, Int)
             -> IO ( Maybe (IntVarName, AstInt AstMethodLet)
                   , AstInt AstMethodLet )
      shareI (i, _) | astIsSmall True i = return (Nothing, i)
      shareI (i, bound) = funToAstIntVarIO (Just (0, fromIntegral bound))
                          $ \ (!varFresh, !astVarFresh) ->
                              (Just (varFresh, i), astVarFresh)
  (bindings, ix2) <- mapAndUnzipM shareI
                     $ zip (Foldable.toList ix) (shsToList $ ixsToShS ix)
  return $! foldr (uncurry astLet)
                  (withKnownShS (ixsToShS ix) $ f $ fromList ix2)
                  (catMaybes bindings)

-- TODO: fuse scatters, scatter and sum, and perhaps more (fromList?)
astScatterS :: forall shm shn shp r s. AstSpan s
            => ShS shn
            -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
            -> (AstVarListS shm, AstIxS AstMethodLet shp)
            -> AstTensor AstMethodLet s (TKS2 (shp ++ shn) r)
astScatterS _shn v (ZS, ZIS) = v
astScatterS shn v (_vars, ix@((:.$) @k (AstConcreteK i) _))
  | not (0 <= i && i < valueOf @k)
  , FTKS _ x <- ftkAst v =
    let ftk = FTKS (ixsToShS ix `shsAppend` shn) x
    in fromPrimal $ astConcrete ftk $ tdefTarget ftk
astScatterS shn v (vars, (:.$) @k (AstConcreteK _) rest)
  | Just Refl <- sameNat (SNat @k) (SNat @1)
  , FTKS _ x <- ftkAst v =
    astReplicate (SNat @1) (STKS (ixsToShS rest `shsAppend` shn) (ftkToSTK x))
    $ astScatterS shn v (vars, rest)
astScatterS shn v (Const var ::$ (vars :: AstVarListS sh3), ix)
  | not $ var `varNameInIxS` ix
  , FTKS _ x <- ftkAst v =
      astScatterS @sh3 @shn @shp shn
        (astSum SNat (STKS (listsToShS vars `shsAppend` shn) (ftkToSTK x)) v)
        (vars, ix)
-- TODO? astScatterS v (ZR, ix) = update (rzero sh 0) ix v
astScatterS shn (Ast.AstFromPrimal v) (vars, ix) =
  Ast.AstFromPrimal $ astScatterS @shm @shn @shp shn v (vars, ix)
astScatterS shn (Ast.AstFromDual v) (vars, ix) =
  Ast.AstFromDual $ astScatterS @shm @shn @shp shn v (vars, ix)
astScatterS shn v (vars, ix) = Ast.AstScatterS @shm @shn @shp shn v (vars, ix)

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
astGatherKnobsS _ _ v0 (!vars0, !_ix0)
  | any (`varNameInAst` v0) $ listsToList vars0 =
    error $ "astGatherS: gather vars in v0: " ++ show (vars0, v0)
astGatherKnobsS knobs shn v0 (ZS, ix0) = astIndexKnobsS knobs shn v0 ix0
astGatherKnobsS _ _ v0 (vars0, ZIS) =
  astReplicateNS @shm @shn (listsToShS vars0) v0
astGatherKnobsS _ shn v0 (vars, AstConcreteK it :.$ _)
  | let i = fromIntegral it
        FTKS (snat :$$ _) x = ftkAst v0
  , not (0 <= i && i < sNatValue snat) =
    let ftk = FTKS (listsToShS vars `shsAppend` shn) x
    in fromPrimal $ astConcrete ftk (tdefTarget ftk)
astGatherKnobsS knobs shn v0 (vars0, i1 :.$ rest1)
  | not (any (`varNameInAst` i1) $ listsToList vars0) =
    astGatherKnobsS @shm @shn
      knobs shn
      (astIndexKnobsS knobs (ixsToShS rest1 `shsAppend` shn) v0 (i1 :.$ ZIS))
      (vars0, rest1)
astGatherKnobsS knobs shn v0 (vars0@(var1 ::$ vars1), ix0)
  | not (getConst var1 `varNameInIxS` ix0) =
    let k :$$ sh' = listsToShS vars0
        FTKS _ x = ftkAst v0
    in astReplicate k (STKS (sh' `shsAppend` shn) (ftkToSTK x))
                    (astGatherKnobsS @(Tail shm) @shn @shp
                                     knobs shn v0 (vars1, ix0))
-- This is only a shorthand not to have to wait for the simplification phase.
astGatherKnobsS knobs shn v0 (vars0@(_ ::$ _), ix0@(_ :.$ _))
  | let ixInit = ixsInit ix0
        varInit = listsInit vars0
        varLast = getConst $ listsLast vars0
  , AstIntVar ixvarLast <- ixsLast ix0
  , ixvarLast == varLast
  , not (varLast `varNameInIxS` ixInit)
  , kLast@SNat <- shsLast (listsToShS vars0)
  , Just Refl <- testEquality kLast (shsLast (ixsToShS ix0)) =
    gcastWith (unsafeCoerceRefl
               :: Init shp ++ (Last shm ': shn) :~: shp ++ shn) $
    gcastWith (unsafeCoerceRefl
               :: Init shm ++ (Last shm ': shn) :~: shm ++ shn) $
    astGatherKnobsS @(Init shm) @(Last shm ': shn) @(Init shp)
                    knobs (kLast :$$ shn) v0 (varInit, ixInit)
astGatherKnobsS knobs shn v0
                (vars, Ast.AstCond (Ast.AstBoolAnd a b) v w :.$ prest) =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shn v0 (vars, i :.$ prest)
astGatherKnobsS knobs shn v0
                (vars, Ast.AstLet varN uN
                         (Ast.AstCond (Ast.AstBoolAnd a b) v w) :.$ prest) =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shn v0 (vars, Ast.AstLet varN uN i :.$ prest)
-- Rules with AstConcreteK on the right hand side of AstPlusK are
-- not needed, thanks to the normal form of AstPlusK rewriting.
astGatherKnobsS knobs shn v0
  (vars, AstPlusK (AstConcreteK i64) i1 :.$ prest)
  | FTKS (SNat @p :$$ _) x <- ftkAst v0 =
    if i64 >= 0 then
      withSNat (fromIntegral i64) $ \(SNat @i) ->
        if i64 > valueOf @p then
          let ftk = FTKS (listsToShS vars `shsAppend` shn) x
          in fromPrimal $ astConcrete ftk (tdefTarget ftk)
        else
          gcastWith (unsafeCoerceRefl :: (i <=? p) :~: True) $
          let v2 = astSliceS (SNat @i) (SNat @(p - i)) (SNat @0) v0
          in astGatherKnobsS knobs shn v2 (vars, i1 :.$ prest)
               -- this gather may still index out of bounds, which is fine
    else
      withSNat (- fromIntegral i64) $ \(SNat @i) ->
        let ftk = FTKS (SNat @i :$$ ixsToShS prest `shsAppend` shn) x
            v2 = fromPrimal (astConcrete ftk (tdefTarget ftk))
                 `astAppendS`
                 v0
        in astGatherKnobsS knobs shn v2 (vars, i1 :.$ prest)
             -- this gather may still index out of bounds, which is fine
astGatherKnobsS knobs shn v0
  (vars, Ast.AstLet varN uN (AstPlusK (AstConcreteK i64) i1) :.$ prest)
  | FTKS (SNat @p :$$ _) x <- ftkAst v0 =
    if i64 >= 0 then
      withSNat (fromIntegral i64) $ \(SNat @i) ->
        if i64 > valueOf @p then
          let ftk = FTKS (listsToShS vars `shsAppend` shn) x
          in fromPrimal $ astConcrete ftk (tdefTarget ftk)
        else
          gcastWith (unsafeCoerceRefl :: (i <=? p) :~: True) $
          let v2 = astSliceS (SNat @i) (SNat @(p - i)) (SNat @0) v0
          in astGatherKnobsS knobs shn v2
                             (vars, Ast.AstLet varN uN i1 :.$ prest)
               -- this gather may still index out of bounds, which is fine
    else
      withSNat (- fromIntegral i64) $ \(SNat @i) ->
        let ftk = FTKS (SNat @i :$$ ixsToShS prest `shsAppend` shn) x
            v2 = fromPrimal (astConcrete ftk (tdefTarget ftk))
                 `astAppendS`
                 v0
        in astGatherKnobsS knobs shn v2 (vars, Ast.AstLet varN uN i1 :.$ prest)
             -- this gather may still index out of bounds, which is fine
astGatherKnobsS knobs shn v0
  ( vars@((::$) @m (Const varm) mrest)
  , Ast.AstCond (AstLeqInt (AstConcreteK j) (AstIntVar varp)) i1 i2
    :.$ prest )
  | varNameToAstVarId varm == varNameToAstVarId varp =
    if | j <= 0 ->
         astGatherKnobsS knobs shn v0 (vars, i1 :.$ prest)
       | j >= valueOf @m ->
         astGatherKnobsS knobs shn v0 (vars, i2 :.$ prest)
       | otherwise ->
         withSNat (fromIntegral j) $ \(SNat @j) ->
         gcastWith (unsafeCoerceRefl :: (j <=? m) :~: True) $
         astLetFun v0 $ \v ->
         -- Unavoidably, prest gets duplicated here. Tough luck.
         -- TODO: so maybe only permit when astIsSmall prest
         -- after we refine astIsSmall and have enough tests to judge
         astGatherKnobsS knobs shn v
           ( (::$) @j (Const varm) mrest
           , i2 :.$ prest )
         `astAppendS`
         astGatherKnobsS knobs shn v
           ( (::$) @(m - j) (Const varm) mrest
           , substituteAstIxS (AstConcreteK j + AstIntVar varm)
                              varm (i1 :.$ prest) )
astGatherKnobsS knobs shn v0
  ( vars@((::$) @m (Const varm) mrest)
  , Ast.AstLet varN uN
      (Ast.AstCond (AstLeqInt (AstConcreteK j) (AstIntVar varp)) i1 i2)
      :.$ prest )
  | varNameToAstVarId varm == varNameToAstVarId varp =
    if | j <= 0 ->
         astGatherKnobsS knobs shn v0 (vars, Ast.AstLet varN uN i1 :.$ prest)
       | j >= valueOf @m ->
         astGatherKnobsS knobs shn v0 (vars, Ast.AstLet varN uN i2 :.$ prest)
       | otherwise ->
         withSNat (fromIntegral j) $ \(SNat @j) ->
         gcastWith (unsafeCoerceRefl :: (j <=? m) :~: True) $
         astLetFun v0 $ \v ->
         -- Both uN and prest gets duplicated here. Tough luck.
         -- TODO: so maybe remove this subcase?
         astGatherKnobsS knobs shn v
           ( (::$) @j (Const varm) mrest
           , Ast.AstLet varN uN i2 :.$ prest )
         `astAppendS`
         astGatherKnobsS knobs shn v
           ( (::$) @(m - j) (Const varm) mrest
           , substituteAstIxS (AstConcreteK j + AstIntVar varm)
                              varm (Ast.AstLet varN uN i1 :.$ prest) )
astGatherKnobsS knobs shn v0
  ( vars@((::$) @m (Const varm) mrest)
  , Ast.AstCond (AstLeqInt (AstConcreteK j)
                           (Ast.AstN1K NegateOp (AstIntVar varp))) i1 i2
    :.$ prest )
  | varNameToAstVarId varm == varNameToAstVarId varp =
    if | - j + 1 <= 0 ->
         astGatherKnobsS knobs shn v0 (vars, i2 :.$ prest)
       | - j + 1 >= valueOf @m ->
         astGatherKnobsS knobs shn v0 (vars, i1 :.$ prest)
       | otherwise ->
         withSNat (- fromIntegral j + 1) $ \(SNat @mj) ->
         gcastWith (unsafeCoerceRefl :: (mj <=? m) :~: True) $
         astLetFun v0 $ \v ->
         astGatherKnobsS knobs shn v
           ( (::$) @mj (Const varm) mrest
           , i1 :.$ prest )
         `astAppendS`
         astGatherKnobsS knobs shn v
           ( (::$) @(m - mj) (Const varm) mrest
           , substituteAstIxS (AstConcreteK (- j + 1) + AstIntVar varm)
                              varm (i2 :.$ prest))
astGatherKnobsS knobs shn v0
  ( vars@((::$) @m (Const varm) mrest)
  , Ast.AstLet varN uN
      (Ast.AstCond (AstLeqInt (AstConcreteK j)
                              (Ast.AstN1K NegateOp (AstIntVar varp))) i1 i2)
    :.$ prest )
  | varNameToAstVarId varm == varNameToAstVarId varp =
    if | - j + 1 <= 0 ->
         astGatherKnobsS knobs shn v0 (vars, Ast.AstLet varN uN i2 :.$ prest)
       | - j + 1 >= valueOf @m ->
         astGatherKnobsS knobs shn v0 (vars, Ast.AstLet varN uN i1 :.$ prest)
       | otherwise ->
         withSNat (- fromIntegral j + 1) $ \(SNat @mj) ->
         gcastWith (unsafeCoerceRefl :: (mj <=? m) :~: True) $
         astLetFun v0 $ \v ->
         astGatherKnobsS knobs shn v
           ( (::$) @mj (Const varm) mrest
           , Ast.AstLet varN uN i1 :.$ prest )
         `astAppendS`
         astGatherKnobsS knobs shn v
           ( (::$) @(m - mj) (Const varm) mrest
           , substituteAstIxS (AstConcreteK (- j + 1) + AstIntVar varm)
                              varm (Ast.AstLet varN uN i2 :.$ prest))
astGatherKnobsS knobs shn v0
  ( (::$) @m (Const varm) mrest
  , (:.$) @p (AstIntVar varp) prest )
  | varm == varp
  , Nothing <- sameNat (Proxy @m) (Proxy @p)
  , FTKS _ x <- ftkAst v0 =
    withSNat (min (valueOf @p) (valueOf @m)) $ \(SNat @m2) ->
      gcastWith (unsafeCoerceRefl :: (m2 <=? p) :~: True) $
      gcastWith (unsafeCoerceRefl :: (m2 <=? m) :~: True) $
      let v2 = astSliceS (SNat @0) (SNat @m2) (SNat @(p - m2)) v0
          ftk = FTKS (SNat @(m - m2) :$$ listsToShS mrest `shsAppend` shn) x
      in astGatherKnobsS knobs shn v2  -- now m2 and p2 are equal
           ((::$) @m2 (Const varm) mrest, AstIntVar varp :.$ prest)
         `astAppendS`
         fromPrimal (astConcrete ftk (tdefTarget ftk))
astGatherKnobsS knobs shn v0
  ( (::$) @m @shmTail (Const varm) mrest
  , (:.$) @p @shpTail (AstIntVar varp) prest )
  | knobPhase knobs == PhaseSimplification  -- prevent a loop
  , varm == varp
  , Just Refl <- sameNat (Proxy @m) (Proxy @p)
  , not (varm `varNameInIxS` prest) =
    Permutation.permFromList (permCycle $ shsLength (listsToShS mrest) + 1)
    $ \(permVars :: Permutation.Perm permVars) ->
    Permutation.permFromList (backpermCycle $ shsLength (ixsToShS prest) + 1)
    $ \(permIx :: Permutation.Perm permIx) ->
       gcastWith (unsafeCoerceRefl
                  :: shm ++ shn
                     :~: Permutation.PermutePrefix
                           permVars (shmTail ++ (m ': shn))) $
       gcastWith (unsafeCoerceRefl
                  :: shpTail ++ (m ': shn)
                     :~: Permutation.PermutePrefix permIx (shp ++ shn)) $
       gcastWith (unsafeCoerceRefl
                  :: (Rank permVars <=? Rank (shmTail ++ (m ': shn)))
                     :~: True) $
       gcastWith (unsafeCoerceRefl
                  :: (Rank permIx <=? Rank (shp ++ shn)) :~: True) $
       fromMaybe (error "astGatherKnobsS: impossible non-permutation")
       $ Permutation.permCheckPermutation permVars
       $ fromMaybe (error "astGatherKnobsS: impossible non-permutation")
       $ Permutation.permCheckPermutation permIx
       $ let v2 = astTransposeS permIx v0
         in astTransposeS
              permVars (astGatherKnobsS knobs (SNat @m :$$ shn)
                                        v2 (mrest, prest))
astGatherKnobsS knobs shn v0
  (vars, ix@(i1 :.$ _))
  | let intInteresting = \case
          Ast.AstCond (Ast.AstBoolAnd{}) _ _ -> True
          AstPlusK (AstConcreteK _) _ -> True
          Ast.AstCond (AstLeqInt AstConcreteK{} (AstIntVar var)) _ _
            | any ((== varNameToAstVarId var) . varNameToAstVarId)
                  (listsToList vars) -> True
          Ast.AstCond (AstLeqInt AstConcreteK{}
                                 (Ast.AstN1K NegateOp (AstIntVar var))) _ _
            | any ((== varNameToAstVarId var) . varNameToAstVarId)
                  (listsToList vars) -> True
          AstIntVar var
            | knobPhase knobs == PhaseSimplification  -- prevent a loop
            , null $ drop 1 $ filter (var `varNameInAst`) (Foldable.toList ix)
            , any ((== varNameToAstVarId var) . varNameToAstVarId)
                  (listsToList vars) -> True
          Ast.AstLet _ _ (Ast.AstCond (Ast.AstBoolAnd{}) _ _) -> True
          Ast.AstLet _ _ (AstPlusK (AstConcreteK _) _) -> True
          Ast.AstLet _ _
            (Ast.AstCond (AstLeqInt AstConcreteK{} (AstIntVar var)) _ _)
            | any ((== varNameToAstVarId var) . varNameToAstVarId)
                  (listsToList vars) -> True
          Ast.AstLet _ _
            (Ast.AstCond (AstLeqInt AstConcreteK{}
                                    (Ast.AstN1K NegateOp (AstIntVar var))) _ _)
            | any ((== varNameToAstVarId var) . varNameToAstVarId)
                  (listsToList vars) -> True
          _ -> False
  , not (intInteresting i1)  -- now vars need to be reordered, too
  , Just i <- findIndex intInteresting
                        (Foldable.toList ix) = assert (i > 0) $
    Permutation.permFromList (backpermCycle $ i + 1)
    $ \(perm :: Permutation.Perm perm) ->
    gcastWith (unsafeCoerceRefl
               :: Permutation.PermutePrefix perm (shp ++ shn)
                  :~: Permutation.PermutePrefix perm shp ++ shn) $
    gcastWith (unsafeCoerceRefl :: (Rank perm <=? Rank (shp ++ shn)) :~: True) $
    fromMaybe (error "astGatherKnobsS: impossible non-permutation")
    $ Permutation.permCheckPermutation perm
    $ let v2 = astTransposeS perm v0
      in astGatherKnobsS knobs shn v2 (vars, ixsPermutePrefix perm ix)
        -- this call is guaranteed to simplify as above, so the tranpose
        -- won't reduce it back to the original and cause a loop
astGatherKnobsS knobs shn v0
  (vars, ix@(i1 :.$ prest))
  | let varInteresting = \case
          Ast.AstCond (AstLeqInt AstConcreteK{} (AstIntVar var)) _ _ ->
            Just var
          Ast.AstCond (AstLeqInt AstConcreteK{}
                                 (Ast.AstN1K NegateOp (AstIntVar var))) _ _ ->
            Just var
          AstIntVar var
            | knobPhase knobs == PhaseSimplification  -- prevent a loop
            , not (var `varNameInIxS` prest) -> Just var
          Ast.AstLet _ _
            (Ast.AstCond (AstLeqInt AstConcreteK{} (AstIntVar var)) _ _) ->
            Just var
          Ast.AstLet _ _
            (Ast.AstCond (AstLeqInt AstConcreteK{}
                                    (Ast.AstN1K NegateOp
                                                (AstIntVar var))) _ _) ->
            Just var
          _ -> Nothing
  , Just varp <- varInteresting i1
  , Just i <- findIndex ((== varNameToAstVarId varp) . varNameToAstVarId)
                        (listsToList vars) = assert (i > 0) $
    Permutation.permFromList (backpermCycle $ i + 1)
    $ \(permWhole :: Permutation.Perm permWhole) ->
    permInverse permWhole $ \(invperm :: Nested.Perm invperm) _ ->
    gcastWith (unsafeCoerceRefl
               :: shm ++ shn
                  :~: Permutation.PermutePrefix permWhole
                        (Permutation.PermutePrefix invperm shm ++ shn)) $
    gcastWith (unsafeCoerceRefl
               :: (Rank permWhole
                   <=? Rank (Permutation.PermutePrefix invperm shm ++ shn))
                  :~: True) $
    fromMaybe (error "astGatherKnobsS: impossible non-permutation")
    $ Permutation.permCheckPermutation permWhole
    $ astTransposeS permWhole
    $ astGatherKnobsS knobs shn v0 (listsPermutePrefix invperm vars, ix)
        -- this call is guaranteed to simplify as above, so the tranpose
        -- won't reduce it back to the original and cause a loop
astGatherKnobsS knobs shn v0 (vars0, ix0@(i1 :.$ rest1)) =
  if | i :.$ rest <- rest1  -- TODO: generalize
     , not (any (`varNameInAst` i) $ listsToList vars0)
     , knobPhase knobs == PhaseSimplification ->  -- prevent a loop
       gcastWith (unsafeCoerceRefl :: (2 <=? Rank (shp ++ shn)) :~: True) $
       astGatherKnobsS @shm @shn
         knobs shn
         (astIndexKnobsS knobs
            (ixsToShS (i1 :.$ rest) `shsAppend` shn)
            (astTransposeS (Permutation.makePerm @'[1, 0]) v0)
            (i :.$ ZIS))
         (vars0, i1 :.$ rest)
     | i2 :.$ i :.$ rest <- rest1
     , not (any (`varNameInAst` i) $ listsToList vars0)
     , knobPhase knobs == PhaseSimplification ->
       gcastWith (unsafeCoerceRefl :: (3 <=? Rank (shp ++ shn)) :~: True) $
       astGatherKnobsS @shm @shn
         knobs shn
         (astIndexKnobsS knobs
            (ixsToShS (i1 :.$ i2 :.$ rest) `shsAppend` shn)
            (astTransposeS (Permutation.makePerm @'[2, 0, 1]) v0)
            (i :.$ ZIS))
         (vars0, i1 :.$ i2 :.$ rest)
     | i2 :.$ i3 :.$ i :.$ rest <- rest1
     , not (any (`varNameInAst` i) $ listsToList vars0)
     , knobPhase knobs == PhaseSimplification ->
       gcastWith (unsafeCoerceRefl :: (4 <=? Rank (shp ++ shn)) :~: True) $
       astGatherKnobsS @shm @shn
         knobs shn
         (astIndexKnobsS knobs
            (ixsToShS (i1 :.$ i2 :.$ i3 :.$ rest) `shsAppend` shn)
            (astTransposeS (Permutation.makePerm @'[3, 0, 1, 2]) v0)
            (i :.$ ZIS))
         (vars0, i1 :.$ i2 :.$ i3 :.$ rest)
     | i2 :.$ i3 :.$ i4 :.$ i :.$ rest <- rest1
     , not (any (`varNameInAst` i) $ listsToList vars0)
     , knobPhase knobs == PhaseSimplification ->
       gcastWith (unsafeCoerceRefl :: (5 <=? Rank (shp ++ shn)) :~: True) $
       astGatherKnobsS @shm @shn
         knobs shn
         (astIndexKnobsS knobs
            (ixsToShS (i1 :.$ i2 :.$ i3 :.$ i4 :.$ rest) `shsAppend` shn)
            (astTransposeS (Permutation.makePerm @'[4, 0, 1, 2, 3]) v0)
            (i :.$ ZIS))
         (vars0, i1 :.$ i2 :.$ i3 :.$ i4 :.$ rest)
     | otherwise -> astGatherCase @shm @shn @shp shn v0 (vars0, ix0)
 where
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
  astGatherCase shn' v4 (!vars4, ix4@((:.$) @_ @shp1' i4 rest4))
   | FTKS _ x <- ftkAst v4 = case v4 of
    Ast.AstProject1{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstProject2{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    {- not possible at this point:
    Ast.AstFromVector _ STKS{} l | AstConcreteK it <- i4 ->
      let i = fromIntegral it
      in astGather @shm' @shn' @shp1' shn' (l V.! i) (vars4, rest4)
    Ast.AstFromVector _ STKScalar l | AstConcreteK it <- i4, ZIS <- rest4 ->
      let i = fromIntegral it
      in astGather @shm' @shn' @shp1' shn' (astSFromK (l V.! i)) (vars4, rest4)
    -}
    {- Ast.AstFromVector{} | gatherFromNF (ixsToShS rest4) vars4 ix4 ->
        -- normal form
      Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4) -}
    {- this rule seems counterproductive in many cases, so disabled until
       we can detect cases where it helps:
    Ast.AstFromVector snat STKS{} l ->
      -- Term rest4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use tlet.
      funToVarsIxS @shm' (listsToShS vars4) $ \ (!varsFresh, IxS !ixFresh) ->
        let f v = astGatherRec @shm' @shn' @shp1' shn' v (vars4, rest4)
            -- This subst doesn't currently break sharing because it's a rename.
            subst i =
              foldr (\(i2, var2) v2 -> substituteAst i2 var2 v2)
                    i
                    (listsToList $ zipSizedS ixFresh vars4)
            i5 = subst i4
       in astGather @shm' @shn' @(p1' ': shm')
                    shn' (astFromVector snat (STKS (listsToShS varsFresh
                                                    `shsAppend` shn')
                                                   (ftkToSTK x))
                          $ V.map f l)
                    (varsFresh, i5 :.$ IxS ixFresh) -}
    Ast.AstFromVector{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    -- This accomplishes fusion if v is a gather or anything
    -- that gather can fuse with, but at the cost of an extra transpose
    -- that doesn't fuse here unless astTransposeAsGatherS is used.
    -- Since the transpose is O(1), let's leave this as is.
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
         fromMaybe (error "astGatherCase: impossible non-permutation")
         $ Permutation.permCheckPermutation perm3S
         $ Permutation.permFromList perm4
         $ \(perm4S :: Permutation.Perm perm4P) ->
         gcastWith (unsafeCoerceRefl
                    :: Compare (Rank perm4P) (Rank (shm' ++ (n1 : shn')))
                       :~: LT) $
         gcastWith (unsafeCoerceRefl
                    :: Permutation.PermutePrefix perm4P (shm' ++ (n1 : shn'))
                       :~: n1 : (shm' ++ shn')) $
         fromMaybe (error "astGatherCase: impossible non-permutation")
         $ Permutation.permCheckPermutation perm4S
         $ let innerGather =
                 astGather @shm' @(n1 : shn') @shp'
                           (snat :$$ shn') (astTransposeS perm3S v) (vars4, ix4)
           in astSum snat (STKS (listsToShS vars4 `shsAppend` shn')
                                (ftkToSTK x))
              $ astTransposeS perm4S innerGather
                {- -- disabled until we can reliably fuse back to transpose
                if not (knobExpand knobs)
                then astTransposeS perm4S innerGather
                else astTransposeAsGatherS knobs perm4S innerGather -}
    -- TODO: the two below are probably wrong, should catch out of bounds
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
    AstConcreteS{} ->
      Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
        -- free variables possible in the index, so can't compute the tensor

    Ast.AstLet var u v ->
      astLet var u (astGather @shm' @shn' @shp' shn' v (vars4, ix4))

    Ast.AstPrimalPart{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstDualPart{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstFromPrimal v ->
      Ast.AstFromPrimal $ astGather @shm' @shn' @shp' shn' v (vars4, ix4)
    Ast.AstFromDual v ->
      Ast.AstFromDual $ astGather @shm' @shn' @shp' shn' v (vars4, ix4)

    AstPlusS{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    AstTimesS{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
      -- Going inside AstTimesS usually makes term more expensive to interpret
      -- and reverting this transformation requires comparing two arguments,
      -- so it's not practical.
    Ast.AstN1S NegateOp v | not (isVar v) ->
      negate (astGatherRec @shm' @shn' @shp' shn' v (vars4, ix4))
        -- TODO: make these go under AstGatherS instead
    Ast.AstN1S AbsOp v | not (isVar v) ->
      abs (astGatherRec @shm' @shn' @shp' shn' v (vars4, ix4))
    Ast.AstN1S SignumOp v | not (isVar v) ->
      signum (astGatherRec @shm' @shn' @shp' shn' v (vars4, ix4))
    Ast.AstN1S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstR1S opCode v | not (isVar v) ->
      Ast.AstR1S opCode (astGatherRec @shm' @shn' @shp' shn' v (vars4, ix4))
    Ast.AstR1S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstR2S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstI2S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstFloorS{} ->  -- see next comment
      Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstFromIntegralS{} ->  -- see next comment
      Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstCastS{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
      -- work would increate otherwise and most probably gather can't
      -- simplify anything that cast could not

    {- is reverted in astGatherKnobsS immediatedly; maybe move to contraction?
    Ast.AstIndexS @shm2 _shn2 v2 (i2 :.$ ZIS) ->
        astGather @shm' @shn' @(shm2 ++ shp') shn' v2 (vars4, i2 :.$ ix4) -}
    Ast.AstIndexS{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstScatterS @shm7 @shn7 @shp7 shn7 v (vars, AstIntVar var5 :.$ ix2)
      | AstIntVar var6 <- i4, var6 == var5 ->
          astGather @shm' @shn' @shp1' shn'
                    (astScatterS @shm7 @shn7 @(Tail shp7) shn7
                                 v (vars, ix2))
                    (vars4, rest4)
    {- not possible at this point:
    Ast.AstScatterS shn7 v (vars, AstConcreteK i5 :.$ ix2)
      | AstConcreteK i6 <- i4 ->
          if i6 == i5
          then astGather @shm' @shn' @shp1' shn'
                         (astScatterS shn7 v (vars, ix2))
                         (vars4, rest4)
          else let ftk = FTKS (listsToShS vars4 `shsAppend` shn') x
               in fromPrimal $ astConcrete ftk (treplTarget 0 ftk) -}
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
                       :: (shm' ++ DropLen shp' shm2) ++ shn2
                          :~: shm' ++ shn') $
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
                       :: (shp2 ++ DropLen shm2 shp') ++ shn'
                          :~: shp2 ++ shn2) $
            let ix42 = IxS $ listsTakeLen vars2 list4
                ix44 = IxS $ listsDropLen vars2 list4
                ix22 = fmap (substLet ix42 vars2) ix2
                ix2244 = ix22 `ixsAppend` ix44
            in astGather shn' v2 (vars4, ix2244)
      in case cmpNat (Proxy @rank4) (Proxy @rank2) of
        LTI -> composedGather
        EQI -> assimilatedGather
        GTI -> gcastWith (flipCompare @rank4 @rank2) assimilatedGather
    Ast.AstMinIndexS @n @sh v -> case ftkAst v of
     FTKS nsh _ -> case shsLast nsh of
      nl@(SNat @nl) ->
        let shnl = shn' `shsAppend` (nl :$$ ZSS)
        in gcastWith (unsafeCoerceRefl
                     :: shp' ++ (shn' ++ '[nl]) :~: n ': sh) $
           gcastWith (unsafeCoerceRefl
                      :: Head (shm' ++ (shn' ++ '[nl]))
                         ': Tail (shm' ++ (shn' ++ '[nl]))
                         :~: shm' ++ (shn' ++ '[nl])) $
           gcastWith (unsafeCoerceRefl
                      :: Init (shm' ++ (shn' ++ '[nl]))
                      :~: shm' ++ shn') $
           Ast.AstMinIndexS @(Head (shm' ++ (shn' ++ '[nl])))
                            @(Tail (shm' ++ (shn' ++ '[nl])))
           $ astGatherKnobsS knobs shnl v (vars4, ix4)
    Ast.AstMaxIndexS @n @sh v -> case ftkAst v of
     FTKS nsh _ -> case shsLast nsh of
      nl@(SNat @nl) ->
        let shnl = shn' `shsAppend` (nl :$$ ZSS)
        in gcastWith (unsafeCoerceRefl
                     :: shp' ++ (shn' ++ '[nl]) :~: n ': sh) $
           gcastWith (unsafeCoerceRefl
                      :: Head (shm' ++ (shn' ++ '[nl]))
                         ': Tail (shm' ++ (shn' ++ '[nl]))
                         :~: shm' ++ (shn' ++ '[nl])) $
           gcastWith (unsafeCoerceRefl
                      :: Init (shm' ++ (shn' ++ '[nl]))
                      :~: shm' ++ shn') $
           Ast.AstMaxIndexS @(Head (shm' ++ (shn' ++ '[nl])))
                            @(Tail (shm' ++ (shn' ++ '[nl])))
           $ astGatherKnobsS knobs shnl v (vars4, ix4)
    {- not possible at this point:
    Ast.AstIotaS{} | AstConcreteK i <- i4 ->
      fromPrimal $ AstConcreteS
      $ Nested.sreplicateScal (listsToShS vars4 `shsAppend` shn')
      $ fromIntegral i -}
    Ast.AstIotaS{} ->  -- probably nothing can be simplified; a normal form
      Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstAppendS{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
      -- fusing would result in gather([gather, gather]), so no gain
    Ast.AstSliceS{}-> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
      -- slicing is O(1) so no point fusing and complicating the expression;
      -- if it did not simplify further with slice, it wouldn't with gather
    Ast.AstReverseS{}-> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
      -- reversing  is O(1)
    Ast.AstTransposeS @perm @sh perm v | FTKS sh _ <- ftkAst v ->
      let rankPerm = Permutation.permRank perm
      in case gcompare (ixsRank ix4) rankPerm of
        GLT ->  -- TODO: this does not provide any proof, so use cmpNat :(
          Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
          {- -- disabled until we can reliably fuse back to transpose
          if knobExpand knobs
          then astGather @shm' @shn' @shp'
                         shn' (astTransposeAsGatherS knobs perm v) (vars4, ix4)
          else Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4) -}
        _ ->
          gcastWith (lemRankMapJust $ shsTakeLen perm sh) $
          gcastWith (unsafeCoerceRefl :: Rank (TakeLen perm sh) :~: Rank perm) $
          permInverse perm
          $ \(invperm :: Nested.Perm invperm) proof ->
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
    Ast.AstReshapeS _sh _v -> {-  -- too hard to fuse back to reshape
      if && knobExpand knobs
      then astGather @shm' @shn' @shp' shn'
                     (astReshapeAsGatherS knobs sh v) (vars4, ix4)
      else -} Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstZipS _v -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstNestS{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstUnNestS _v -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)

    Ast.AstFromS stkz v -> case sameSTK (ftkToSTK (ftkAst v)) stkz of
      Just Refl -> astGather @shm' @shn' @shp' shn' v (vars4, ix4)
        -- rare, usually simplifies away earlier
      Nothing -> error "astGatherCase: wrong tensor kinds in AstFromS"
    -- These conversions need to stay down.
    Ast.AstSFromR{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstSFromX{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)

    -- These should not appear here unless via wacky tests.
    Ast.AstDot1InS{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)
    Ast.AstMatmul2S{} -> Ast.AstGatherS @shm' @shn' @shp' shn' v4 (vars4, ix4)

astAppendS :: AstSpan s
           => AstTensor AstMethodLet s (TKS2 (m ': sh) r)
           -> AstTensor AstMethodLet s (TKS2 (n ': sh) r)
           -> AstTensor AstMethodLet s (TKS2 ((m + n) ': sh) r)
astAppendS u v | FTKS (SNat' @0 :$$ _) _ <- ftkAst u = v
astAppendS u v | FTKS (SNat' @0 :$$ _) _ <- ftkAst v = u
astAppendS (Ast.AstFromVector (SNat @k1) stk2@STKS{} l1)
           (Ast.AstFromVector (SNat @k2) STKS{} l2) =
  astFromVector (SNat @(k1 + k2)) stk2 $ l1 V.++ l2
astAppendS (Ast.AstFromVector (SNat @k1) stk2@STKScalar l1)
           (Ast.AstFromVector (SNat @k2) STKScalar l2) =
  astFromVector (SNat @(k1 + k2)) stk2 $ l1 V.++ l2
astAppendS (Ast.AstFromPrimal u) (Ast.AstFromPrimal v) =
  Ast.AstFromPrimal $ astAppendS u v
astAppendS (Ast.AstFromDual u) (Ast.AstFromDual v) =
  Ast.AstFromDual $ astAppendS u v
astAppendS u v = Ast.AstAppendS u v

astSliceS :: forall i n k sh s r. AstSpan s
          => SNat i -> SNat n -> SNat k
          -> AstTensor AstMethodLet s (TKS2 (i + n + k ': sh) r)
          -> AstTensor AstMethodLet s (TKS2 (n ': sh) r)
astSliceS SNat SNat SNat (Ast.AstFromVector _ stk@STKS{} l) =
  astFromVector (SNat @n) stk $ V.take (valueOf @n) $ V.drop (valueOf @i) l
astSliceS SNat SNat SNat (Ast.AstFromVector _ stk@STKScalar l) =
  astFromVector (SNat @n) stk $ V.take (valueOf @n) $ V.drop (valueOf @i) l
astSliceS SNat SNat SNat (Ast.AstReplicate _ stk@STKS{} v) =
  astReplicate (SNat @n) stk v
astSliceS SNat SNat SNat (Ast.AstReplicate _ stk@STKScalar v) =
  astReplicate (SNat @n) stk v
astSliceS (SNat' @0) SNat (SNat' @0) v = v
astSliceS SNat (SNat' @1) SNat v | FTKS (_ :$$ sh) x <- ftkAst v =
  astReplicate (SNat @1) (STKS sh (ftkToSTK x))
               (astIndexS sh v (valueOf @i :.$ ZIS))
astSliceS SNat SNat SNat (Ast.AstGatherS shn v (Const var ::$ vars, ix)) =
  let ivar = valueOf @i + AstIntVar var
      ix2 = substituteAstIxS ivar var ix  -- cheap subst, because ivar is tiny
  in astGatherS shn v (Const var ::$ vars, ix2)
astSliceS i n@(SNat @n0) _k (Ast.AstAppendS v1 v2)
  | FTKS (m1@(SNat @m1) :$$ _) _ <- ftkAst v1
  , FTKS (m2@(SNat @m2) :$$ _) _ <- ftkAst v2 =
    let i1 = sNatValue i `min` sNatValue m1
        n1 = sNatValue n `min` (sNatValue m1 - i1)
        k1 = sNatValue m1 - i1 - n1
        i2' = sNatValue i `max` sNatValue m1
        i2 = i2' - sNatValue m1
        n2 = sNatValue n - n1
        k2 = sNatValue m2 - i2 - n2
    in withSNat i1 $ \si1@(SNat @i1) ->
       withSNat n1 $ \sn1@(SNat @n1) ->
       withSNat k1 $ \sk1@(SNat @k1) ->
       withSNat i2 $ \si2@(SNat @i2) ->
       withSNat n2 $ \sn2@(SNat @n2) ->
       withSNat k2 $ \sk2@(SNat @k2) ->
         gcastWith (unsafeCoerceRefl :: n1 + n2 :~: n0) $
         gcastWith (unsafeCoerceRefl :: i1 + n1 + k1 :~: m1) $
         gcastWith (unsafeCoerceRefl :: i2 + n2 + k2 :~: m2) $
         astAppendS (astSliceS si1 sn1 sk1 v1) (astSliceS si2 sn2 sk2 v2)
astSliceS i n k (Ast.AstSliceS i2 _n2 k2 v) =
  astSliceS (snatPlus i i2) n (snatPlus k k2) v
astSliceS i n k (Ast.AstReverseS v) = astReverseS (astSliceS k n i v)
astSliceS i n k v1 = case v1 of
  Ast.AstCond b a2 a3 ->
    astCond b (astSliceS i n k a2) (astSliceS i n k a3)
  Ast.AstLet var u v -> astLet var u (astSliceS i n k v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astSliceS i n k v
  Ast.AstFromDual v -> Ast.AstFromDual $ astSliceS i n k v
  AstPlusS u v -> astSliceS i n k u + astSliceS i n k v
  AstTimesS u v -> astSliceS i n k u * astSliceS i n k v
  Ast.AstN1S NegateOp u -> negate (astSliceS i n k u)
  Ast.AstN1S AbsOp u -> abs (astSliceS i n k u)
  Ast.AstN1S SignumOp u -> signum (astSliceS i n k u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astSliceS i n k u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (astSliceS i n k u)
                                             (astSliceS i n k v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (astSliceS i n k u)
                                             (astSliceS i n k v)
  Ast.AstFloorS a -> astFloorS $ astSliceS i n k a
  Ast.AstFromIntegralS v -> astFromIntegralS $ astSliceS i n k v
  Ast.AstCastS v -> astCastS $ astSliceS i n k v
  _ -> Ast.AstSliceS i n k v1

astReverseS :: forall n sh s r. AstSpan s
            => AstTensor AstMethodLet s (TKS2 (n ': sh) r)
            -> AstTensor AstMethodLet s (TKS2 (n ': sh) r)
astReverseS (Ast.AstFromVector snat stk l) =
  astFromVector snat stk $ V.reverse l
astReverseS (Ast.AstReplicate snat stk v) = astReplicate snat stk v
astReverseS (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astReverseS v
astReverseS (Ast.AstFromDual v) = Ast.AstFromDual $ astReverseS v
astReverseS (Ast.AstGatherS @shm @shn @shp
                            shn v ((::$) @k (Const var) vars, ix)) =
  let ivar = valueOf @k - AstIntVar var
      ix2 = substituteAstIxS ivar var ix  -- cheap subst, because ivar is tiny
  in astGatherS @shm @shn @shp shn v (Const var ::$ vars, ix2)
astReverseS (Ast.AstReverseS v) = v
astReverseS v = Ast.AstReverseS v

-- TODO: try to completely cover the AstGatherS case here, which would permit
-- not expanding to astTransposeAsGatherS in astGatherCase
-- | Beware, this does not do full simplification, which often requires
-- the gather form, so astTransposeAsGather needs to be called in addition
-- if full simplification is required.
astTransposeS
  :: forall perm sh s r.
     (Permutation.IsPermutation perm, Rank perm <= Rank sh, AstSpan s)
  => Permutation.Perm perm -> AstTensor AstMethodLet s (TKS2 sh r)
  -> AstTensor AstMethodLet s (TKS2 (Permutation.PermutePrefix perm sh) r)
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
                 :: Permutation.PermutePrefix
                      (0 : Permutation.MapSucc perm) (n : sh)
                    :~: n : Permutation.PermutePrefix perm sh) $
      fromMaybe (error "astTransposeS: impossible non-permutation")
      $ Permutation.permCheckPermutation zsuccP
      $ astSum snat (STKS (shsPermutePrefix perm sh) x) $ astTransposeS zsuccP v
  Ast.AstReplicate snat@(SNat @n) (STKS @sh3 sh3 _) _
    | Just u2 <- unRepl t
    , Refl <- lemAppNil @(Permutation.PermutePrefix perm (n : sh3)) ->
      astReplicateNS (shsPermutePrefix perm (snat :$$ sh3)) u2
  Ast.AstReplicate snat1@SNat _  -- nesting 4 is probably already an overkill
    (Ast.AstReplicate snat2@SNat _
      (Ast.AstReplicate snat3@SNat _
        (Ast.AstReplicate snat4@SNat STKS{} u)))
    | _ `PCons` _ `PCons` _ `PCons` _ `PCons` PNil <- perm ->
      astReplicateNS
        (shsPermutePrefix perm (snat1 :$$ snat2 :$$ snat3 :$$ snat4 :$$ ZSS)) u
  Ast.AstReplicate snat1@SNat _
    (Ast.AstReplicate snat2@SNat _
      (Ast.AstReplicate snat3@SNat _
        (Ast.AstReplicate snat4@SNat STKScalar u)))
    | _ `PCons` _ `PCons` _ `PCons` _ `PCons` PNil <- perm ->
      astReplicateNS
        (shsPermutePrefix perm (snat1 :$$ snat2 :$$ snat3 :$$ snat4 :$$ ZSS))
        (astSFromK u)
  Ast.AstReplicate snat1@SNat _
    (Ast.AstReplicate snat2@SNat _
      (Ast.AstReplicate snat3@SNat STKS{} u))
    | _ `PCons` _ `PCons` _ `PCons` PNil <- perm ->
      astReplicateNS
        (shsPermutePrefix perm (snat1 :$$ snat2 :$$ snat3 :$$ ZSS)) u
  Ast.AstReplicate snat1@SNat _
    (Ast.AstReplicate snat2@SNat _
      (Ast.AstReplicate snat3@SNat STKScalar u))
    | _ `PCons` _ `PCons` _ `PCons` PNil <- perm ->
      astReplicateNS
        (shsPermutePrefix perm (snat1 :$$ snat2 :$$ snat3 :$$ ZSS))
        (astSFromK u)
  Ast.AstReplicate snat1@SNat _ (Ast.AstReplicate snat2@SNat STKS{} u)
    | _ `PCons` _ `PCons` PNil <- perm ->
      astReplicateNS (shsPermutePrefix perm (snat1 :$$ snat2 :$$ ZSS)) u
  Ast.AstReplicate snat1@SNat _ (Ast.AstReplicate snat2@SNat STKScalar u)
    | _ `PCons` _ `PCons` PNil <- perm ->
      astReplicateNS (shsPermutePrefix perm (snat1 :$$ snat2 :$$ ZSS))
                     (astSFromK u)
  AstConcreteS v -> astConcreteS (tstranspose perm $ Concrete v)

  Ast.AstLet var u v -> astLet var u (astTransposeS perm v)

  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astTransposeS perm v
  Ast.AstFromDual v -> Ast.AstFromDual $ astTransposeS perm v

  AstPlusS u v -> astTransposeS perm u + astTransposeS perm v
  AstTimesS u v -> astTransposeS perm u * astTransposeS perm v
  Ast.AstN1S NegateOp u -> negate (astTransposeS perm u)
  Ast.AstN1S AbsOp u -> abs (astTransposeS perm u)
  Ast.AstN1S SignumOp u -> signum (astTransposeS perm u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astTransposeS perm u)
  Ast.AstR2S opCode u v ->
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
            vars2 = listsPermutePrefix perm vars
        in gcastWith (unsafeCoerceRefl
                      :: Permutation.PermutePrefix perm shm ++ shn
                         :~: Permutation.PermutePrefix perm (shm ++ shn)) $
           astGatherS @(Permutation.PermutePrefix perm shm) @shn @shp
                      shn v (vars2, ix)
  Ast.AstTransposeS @_ @sh2 perm2 u | FTKS sh2 _ <- ftkAst u ->
    -- TODO: try to perform at type level
    let permV = Permutation.permToList' perm
        perm2V = Permutation.permToList' perm2
        perm2Matched =
          perm2V
          ++ take (length permV - length perm2V) (drop (length perm2V) [0 ..])
        perm3V = normalizePermutationHack
                 $ backpermutePrefixList permV perm2Matched
    in Permutation.permFromList perm3V $ \(perm3 :: Permutation.Perm perm3) ->
      fromMaybe (error "astTransposeS: impossible non-permutation")
      $ Permutation.permCheckPermutation perm3
      $ gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix perm3 sh2
                      :~: Permutation.PermutePrefix perm sh) $
        case compare (length perm3V) (shsLength sh2) of
          LT -> gcastWith (unsafeCoerceRefl
                           :: Compare (Rank perm3) (Rank sh2) :~: LT) $
                astTransposeS perm3 u
          EQ -> gcastWith (unsafeCoerceRefl
                           :: Compare (Rank perm3) (Rank sh2) :~: EQ) $
                astTransposeS perm3 u
          GT -> error "astTransposeS: GT"
  u -> Ast.AstTransposeS perm u

-- TODO: try to cover the AstGatherS case here, which would permit
-- not expanding to astReshapeAsGatherS in astGatherCase
-- | Beware, this does not do full simplification, which often requires
-- the gather form, so astReshapeAsGather needs to be called in addition
-- if full simplification is required.
astReshapeS :: forall sh sh2 x s. (Product sh ~ Product sh2, AstSpan s)
            => ShS sh2 -> AstTensor AstMethodLet s (TKS2 sh x)
            -> AstTensor AstMethodLet s (TKS2 sh2 x)
astReshapeS sh2 t = case t of
  Ast.AstReplicate (SNat' @1) STKS{} x -> astReshapeS sh2 x
  Ast.AstReplicate (SNat' @1) STKScalar x -> astReshapeS sh2 (astSFromK x)
  Ast.AstReplicate _ STKS{} _ | Just u2 <- unRepl t
                              , Refl <- lemAppNil @sh2 ->
    astReplicateNS sh2 u2
  Ast.AstReplicate _ STKScalar u | Refl <- lemAppNil @sh2 ->
    astReplicateNS sh2 (astSFromK u)
  Ast.AstReplicate k (STKS @sh1 _ x) u | (:$$) @_ @rest2 k2 rest2 <- sh2
                                       , Just Refl <- testEquality k k2 ->
    gcastWith (unsafeCoerceRefl :: Product rest2 :~: Product sh1) $
    astReplicate k (STKS rest2 x) $ astReshapeS rest2 u
  Ast.AstLet var u v -> astLet var u (astReshapeS @_ @sh2 sh2 v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astReshapeS sh2 v
  Ast.AstFromDual v -> Ast.AstFromDual $ astReshapeS sh2 v
  -- Reshaping can be costly, so we don't touch AstTimesS, etc.
  Ast.AstN1S NegateOp u -> negate (astReshapeS @_ @sh2 sh2 u)
  Ast.AstN1S AbsOp u -> abs (astReshapeS @_ @sh2 sh2 u)
  Ast.AstN1S SignumOp u -> signum (astReshapeS @_ @sh2 sh2 u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astReshapeS @_ @sh2 sh2 u)
  Ast.AstReshapeS _ v -> astReshapeS @_ @sh2 sh2 v
  _ | FTKS sh _ <- ftkAst t -> case testEquality sh sh2 of
    Just Refl -> t
    _ -> Ast.AstReshapeS sh2 t

-- Beware that increasing the number of calls to this constructor
-- sometimes increases runtime, because not enough copies cancel out.
-- Hence the commented out rules below.
astNestS
  :: forall sh1 sh2 x ms s. AstSpan s
  => ShS sh1 -> ShS sh2
  -> AstTensor ms s (TKS2 (sh1 ++ sh2) x)
  -> AstTensor ms s (TKS2 sh1 (TKS2 sh2 x))
astNestS sh1 sh2 t = case t of
--  Ast.AstCond b v1 v2 ->
--    Ast.AstCond b (astNestS sh1 sh2 v1) (astNestS sh1 sh2 v2)  -- TODO: ??
  Ast.AstLet var u2 d2 ->
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
--  Ast.AstCond b v1 v2 ->
--    Ast.AstCond b (astUnNestS v1) (astUnNestS v2)  -- TODO: ??
  Ast.AstLet var u2 d2 ->
    astLet var u2 (astUnNestS d2)
  Ast.AstFromPrimal u ->
    Ast.AstFromPrimal $ astUnNestS u
  Ast.AstFromDual u ->
    Ast.AstFromDual $ astUnNestS u
--  Ast.AstNestS u -> u
  _ -> Ast.AstUnNestS t

astFromS :: forall y z s.
            SingletonTK z -> AstTensor AstMethodLet s y
         -> AstTensor AstMethodLet s z
astFromS stkz v | Just Refl <- sameSTK (ftkToSTK (ftkAst v)) stkz = v
astFromS STKScalar (Ast.AstCond b v1 v2) =
  Ast.AstCond b (astFromS STKScalar v1) (astFromS STKScalar v2)
  -- a rare case where we don't push up but down
astFromS (STKScalar @r1) (AstConcreteS @r2 v)
  | ZSS <- Nested.sshape v
  , Just Refl <- testEquality (typeRep @r1) (typeRep @r2) =
    AstConcreteK (Nested.sunScalar v)
astFromS stkz (Ast.AstFromPrimal v) =
  Ast.AstFromPrimal $ astFromS stkz v
  -- a rare case where we don't push up but down so that conversions
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
         => SingletonTK z -> AstTensor AstMethodLet s y
         -> AstTensor AstMethodLet s z
astSFrom stkz (Ast.AstFromS _ v)  -- shortcut
         | Just Refl <- sameSTK (ftkToSTK (ftkAst v)) stkz = v
astSFrom stkz v = case (stkz, ftkToSTK (ftkAst v)) of
  (_, stky) | Just Refl <- sameSTK stky stkz -> v
  (STKS ZSS (STKScalar @rz), STKScalar @ry) ->
    case testEquality (typeRep @ry) (typeRep @rz) of
      Just Refl -> astSFromK v
      Nothing -> error "astSFrom: tensor kinds don't match"
  (STKS shz zx, STKR yn yx) ->
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
  Ast.AstCond b a2 a3 -> astCond b (astSFromK a2) (astSFromK a3)
  AstConcreteK k -> AstConcreteS $ Nested.sscalar k
  Ast.AstFromPrimal v -> Ast.AstFromPrimal $ astSFromK v
  Ast.AstFromDual v -> Ast.AstFromDual $ astSFromK v
  AstPlusK u v -> astSFromK u + astSFromK v
  AstTimesK u v -> astSFromK u * astSFromK v
  Ast.AstN1K NegateOp u -> negate (astSFromK u)
  Ast.AstN1K AbsOp u -> abs (astSFromK u)
  Ast.AstN1K SignumOp u -> signum (astSFromK u)
-- TODO:  Ast.AstR1K opCode u -> Ast.AstR1S opCode (astSFromK u)
-- TODO:  Ast.AstR2K opCode u v -> Ast.AstR2S opCode (astSFromK u) (astSFromK v)
  Ast.AstI2K opCode u v -> Ast.AstI2S opCode (astSFromK u) (astSFromK v)
  Ast.AstFromS _ v ->
    case matchingFTK (ftkAst v) (FTKS ZSS (FTKScalar @r)) of
      Just Refl -> v
      _ -> error "astSFromK: unexpected tensor kinds"
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
  Ast.AstFromVector snat@SNat (STKR _ x) l -> case sh of
   snat2 :$$ rest | Just Refl <- sameNat snat snat2 ->
     astFromVector snat (STKS rest x) (V.map (astSFromR rest) l)
   _ -> error "astSFromR: impossible shape"
  Ast.AstSum snat@SNat (STKR _ x) a ->
    astSum snat (STKS sh x) (astSFromR (snat :$$ sh) a)
  Ast.AstReplicate snat@SNat (STKR _ x) a -> case sh of
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

  Ast.AstLet var u v -> astLet var u (astSFromR sh v)

  Ast.AstPrimalPart a -> astPrimalPart $ astSFromR sh a
  Ast.AstDualPart a -> astDualPart $ astSFromR sh a
  Ast.AstFromPrimal a -> Ast.AstFromPrimal $ astSFromR sh a
  Ast.AstFromDual a -> Ast.AstFromDual $ astSFromR sh a

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
astSFromX sh (Ast.AstFromPrimal v) = Ast.AstFromPrimal $ astSFromX sh v
astSFromX sh (Ast.AstFromDual v) = Ast.AstFromDual $ astSFromX sh v
astSFromX sh w@(Ast.AstFromS _ v) | FTKX _ x <- ftkAst w =
  case matchingFTK (FTKS sh x) (ftkAst v) of
    Just Refl -> v
    _ -> error "astSFromX: different shapes in AstSFromX(AstFromS)"
astSFromX sh v = Ast.AstSFromX sh v


-- * ConvertTensor instances needed for unwinding in astConcrete

instance AstSpan s => ConvertTensor (AstTensor AstMethodLet s) where
  rzip @y @z a = case ftkAst a of
    FTKProduct (FTKR sh' y) (FTKR _ z) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        astLetFun a $ \a3 ->
          let (a31, a32) = tunpairConv a3
          in astFromS @(TKS2 sh (TKProduct y z))
                      (STKR (shrRank sh')
                            (STKProduct (ftkToSTK y) (ftkToSTK z)))
             $ Ast.AstZipS $ astPair (astSFromR @sh sh a31)
                                     (astSFromR @sh sh a32)
  runzip @y @z a = case ftkAst a of
    FTKR sh' (FTKProduct y z) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        astLetFun (Ast.AstUnzipS $ astSFromR @sh sh a) $ \b3 ->
          let (b31, b32) = tunpairConv b3
          in astPair (astFromS @(TKS2 sh y)
                               (STKR (shrRank sh') (ftkToSTK y)) b31)
                     (astFromS @(TKS2 sh z)
                               (STKR (shrRank sh') (ftkToSTK z)) b32)
  szip = Ast.AstZipS
  sunzip = Ast.AstUnzipS
  xzip @y @z @sh' a = case ftkAst a of
    FTKProduct (FTKX sh' y) (FTKX _ z) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        astLetFun a $ \a3 ->
          let (a31, a32) = tunpairConv a3
          in astFromS @(TKS2 sh (TKProduct y z))
                      (STKX (ssxFromShape sh')
                            (STKProduct (ftkToSTK y) (ftkToSTK z)))
             $ Ast.AstZipS $ astPair (astSFromX @sh @sh' sh a31)
                                     (astSFromX @sh @sh' sh a32)
  xunzip @y @z @sh' a = case ftkAst a of
    FTKX sh' (FTKProduct y z) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        astLetFun (Ast.AstUnzipS $ astSFromX @sh @sh' sh a) $ \b3 ->
          let (b31, b32) = tunpairConv b3
          in astPair (astFromS @(TKS2 sh y)
                               (STKX (ssxFromShape sh') (ftkToSTK y)) b31)
                     (astFromS @(TKS2 sh z)
                               (STKX (ssxFromShape sh') (ftkToSTK z)) b32)

  tfromS = astFromS
  rfromX a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        rfromS $ sfromX @_ @sh a
  xfromR a = case ftkAst a of
    FTKR shr _ ->
      withCastRS shr $ \(sh :: ShS sh) ->
        withKnownShS sh $
        xfromS @_ @sh $ sfromR a

  sfromK = astSFromK
  sfromR = astSFromR knownShS
  sfromX = astSFromX knownShS

  xnestR @sh1' @m @x sh1' a = case ftkAst a of
    FTKX sh1sh2' x | SNat <- ssxRank sh1' ->
      withCastXS sh1sh2' $ \(sh1sh2 :: ShS sh1sh2) ->
        withKnownShS sh1sh2 $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1') sh1sh2 ++ Drop (Rank sh1') sh1sh2
                      :~: sh1sh2) $
        (unsafeCoerce
           :: AstTensor AstMethodLet s
                (TKX2 sh1' (TKS2 (Drop (Rank sh1') sh1sh2) x))
           -> AstTensor AstMethodLet s (TKX2 sh1' (TKR2 m x)))
        $ astFromS @(TKS2 (Take (Rank sh1') sh1sh2)
                          (TKS2 (Drop (Rank sh1') sh1sh2) x))
                   (STKX sh1' (STKS (dropShS @(Rank sh1') sh1sh2) (ftkToSTK x)))
        $ astNestS (takeShS @(Rank sh1') sh1sh2) (dropShS @(Rank sh1') sh1sh2)
        $ astSFromX @sh1sh2 sh1sh2 a
  xnestS @sh1' @sh2 @x sh1' a = case ftkAst a of
    FTKX sh1sh2' x | SNat <- ssxRank sh1' ->
      withCastXS sh1sh2' $ \(sh1sh2 :: ShS sh1sh2) ->
        withKnownShS sh1sh2 $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1') sh1sh2 ++ sh2
                      :~: sh1sh2) $
        astFromS @(TKS2 (Take (Rank sh1') sh1sh2) (TKS2 sh2 x))
                 (STKX sh1' (STKS knownShS (ftkToSTK x)))
        $ astNestS @_ @sh2 (takeShS @(Rank sh1') sh1sh2) knownShS
        $ astSFromX @sh1sh2 sh1sh2 a
  xnest @sh1' @sh2' @x sh1' a = case ftkAst a of
    FTKX sh1sh2' x | SNat <- ssxRank sh1' ->
      withCastXS sh1sh2' $ \(sh1sh2 :: ShS sh1sh2) ->
        withKnownShS sh1sh2 $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1') sh1sh2 ++ Drop (Rank sh1') sh1sh2
                      :~: sh1sh2) $
        (unsafeCoerce
           :: AstTensor AstMethodLet s
                (TKX2 sh1' (TKS2 (Drop (Rank sh1') sh1sh2) x))
           -> AstTensor AstMethodLet s (TKX2 sh1' (TKX2 sh2' x)))
        $ astFromS @(TKS2 (Take (Rank sh1') sh1sh2)
                          (TKS2 (Drop (Rank sh1') sh1sh2) x))
                   (STKX sh1' (STKS (dropShS @(Rank sh1') sh1sh2) (ftkToSTK x)))
        $ astNestS (takeShS @(Rank sh1') sh1sh2) (dropShS @(Rank sh1') sh1sh2)
        $ astSFromX @sh1sh2 sh1sh2 a
  xunNestR @sh1' @m @x a = case ftkAst a of
    FTKX sh1' y -> case y of
      FTKR sh2' x ->
        withCastXS sh1' $ \(sh1 :: ShS sh1) ->
        withCastRS sh2' $ \(_ :: ShS sh2) ->
          astFromS @(TKS2 (sh1 ++ sh2) x)
                   (STKX (ssxFromShape sh1' `ssxAppend` ssxReplicate (SNat @m))
                         (ftkToSTK x))
          $ astUnNestS @sh1 @sh2
          $ astSFromX @sh1 sh1
          $ (unsafeCoerce
             :: AstTensor AstMethodLet s (TKX2 sh1' (TKR2 m x))
             -> AstTensor AstMethodLet s (TKX2 sh1' (TKS2 sh2 x)))
            a
  xunNestS @_ @sh2 @x a = case ftkAst a of
    FTKX sh1' y -> case y of
      FTKS _ x ->
        withCastXS sh1' $ \(sh1 :: ShS sh1) ->
          astFromS @(TKS2 (sh1 ++ sh2) x)
                   (STKX (ssxFromShape sh1'
                          `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2)))
                         (ftkToSTK x))
          $ astUnNestS @sh1 @sh2
          $ astSFromX @sh1 sh1 a
  xunNest @sh1' @sh2' @x a = case ftkAst a of
    FTKX sh1' y -> case y of
      FTKX sh2' x ->
        withCastXS sh1' $ \(sh1 :: ShS sh1) ->
        withCastXS sh2' $ \(_ :: ShS sh2) ->
          astFromS @(TKS2 (sh1 ++ sh2) x)
                   (STKX (ssxFromShape sh1' `ssxAppend` ssxFromShape sh2')
                         (ftkToSTK x))
          $ astUnNestS @sh1 @sh2
          $ astSFromX @sh1 sh1
          $ (unsafeCoerce
             :: AstTensor AstMethodLet s (TKX2 sh1' (TKX2 sh2' x))
             -> AstTensor AstMethodLet s (TKX2 sh1' (TKS2 sh2 x)))
            a

  tpairConv = astPair
  tunpairConv t = (astProject1 t, astProject2 t)


-- * Helper combinators

-- All but the last case are shortcuts for common forms.
astConcrete :: FullShapeTK y -> Concrete y
            -> AstTensor AstMethodLet PrimalSpan y
astConcrete ftk v = case ftk of
  FTKScalar -> astConcreteK v
  FTKR sh' FTKScalar ->
    withCastRS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      astFromS (ftkToSTK ftk) $ astConcreteS (sfromR @_ @sh v)
  FTKS _ FTKScalar -> astConcreteS v
  FTKX sh' FTKScalar ->
    withCastXS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      astFromS (ftkToSTK ftk) $ astConcreteS (sfromX @_ @sh v)
  FTKProduct ftk1 ftk2 ->
    astPair (astConcrete ftk1 (tproject1 v)) (astConcrete ftk2 (tproject2 v))
  _ -> concreteTarget astConcreteK astConcreteS astFromS (ftkToSTK ftk) v

-- TODO: check if we ever have variables bounds to apply.
astLetFun :: forall y z s s2. (AstSpan s, AstSpan s2)
          => AstTensor AstMethodLet s y
          -> (AstTensor AstMethodLet s y -> AstTensor AstMethodLet s2 z)
          -> AstTensor AstMethodLet s2 z
astLetFun a f | astIsSmall True a = f a
astLetFun a f = case a of
  Ast.AstFromS @y2 stkz v ->
    let (var, ast) = funToAst2 (ftkAst v) Nothing (f . astFromS @y2 stkz)
    in astLet var v ast
  _ -> case ftkAst a of
    ftk@(FTKR @_ @x sh' x) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        let (var, ast) =
              funToAst2 (FTKS sh x) Nothing
                        (f . astFromS @(TKS2 sh x) (ftkToSTK ftk))
        in astLet var (astSFromR sh a) ast
             -- safe, because subsitution ruled out above
    ftk@(FTKX @_ @x sh' x) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        let (var, ast) =
              funToAst2 (FTKS sh x) Nothing
                        (f . astFromS @(TKS2 sh x) (ftkToSTK ftk))
        in astLet var (astSFromX sh a) ast
    -- calling recursively for product may be not worth it
    ftk -> let (var, ast) = funToAst2 ftk Nothing f
           in astLet var a ast

astReplicateNS :: forall shn shp s x. AstSpan s
               => ShS shn -> AstTensor AstMethodLet s (TKS2 shp x)
               -> AstTensor AstMethodLet s (TKS2 (shn ++ shp) x)
astReplicateNS shn v | STKS shp x <- ftkToSTK (ftkAst v) =
  let go :: ShS shn' -> AstTensor AstMethodLet s (TKS2 (shn' ++ shp) x)
      go ZSS = v
      go (snat :$$ shn2) =
        astReplicate snat (STKS (shn2 `shsAppend` shp) x) $ go shn2
  in go shn

unRepl :: AstSpan s
       => AstTensor AstMethodLet s (TKS2 sh x)
       -> Maybe (AstTensor AstMethodLet s (TKS2 '[] x))
unRepl (Ast.AstReplicate _ (STKS ZSS _) u) = Just u
unRepl (Ast.AstReplicate _ STKScalar u) = Just $ astSFromK u
unRepl (Ast.AstReplicate _ STKS{} u) = unRepl u
unRepl _ = Nothing


-- * A cheap simplification of only the topmost nodes

-- | This does a single step of simplification of any non-indexing term
-- (many steps if guaranteed net beneficial). Terms representing integers
-- and 'AstBool' terms are simplified as much as possible.
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
  Ast.AstMapAccumRDer k bftk eftk f df rf acc0 es ->
    astMapAccumRDer k bftk eftk f df rf acc0 es
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    astMapAccumLDer k bftk eftk f df rf acc0 es
  Ast.AstApply v ll -> astApply v ll
  Ast.AstVar{} -> t
  Ast.AstCond a b c -> astCond a b c
  Ast.AstBuild1{} -> t

  Ast.AstLet var u v -> astLet var u v

  Ast.AstPrimalPart v -> astPrimalPart v  -- has to be done sooner or later
  Ast.AstDualPart v -> astDualPart v
  Ast.AstFromPrimal{} -> t
  Ast.AstFromDual{} -> t

  AstPlusK{} -> t  -- already reduced upon creation in CarriersAst
  AstTimesK{} -> t
  Ast.AstN1K{} -> t
  Ast.AstR1K{} -> t
  Ast.AstR2K{} -> t
  Ast.AstI2K{} -> t
  AstConcreteK k -> AstConcreteK k
  Ast.AstFloorK v -> astFloorK v
  Ast.AstFromIntegralK v -> astFromIntegralK v
  Ast.AstCastK v -> astCastK v

  AstPlusS{} -> t
  AstTimesS{} -> t
  Ast.AstN1S{} -> t
  Ast.AstR1S{} -> t
  Ast.AstR2S{} -> t
  Ast.AstI2S{} -> t
  AstConcreteS a -> AstConcreteS a
  Ast.AstFloorS v -> astFloorS v
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
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatmul2S{} -> t


-- * The expansion (e.g., into gather expressions) bottom-up pass

-- TODO: perhaps move this and contractAst to separate modules

expandAstInt :: AstInt AstMethodLet -> AstInt AstMethodLet
expandAstInt = expandAst

expandAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
expandAstIxS = fmap expandAstInt

-- | This pass expands terms, e.g., into @AstGather@ terms, in order
-- to expose redexes and enable fusion. It assumes that a contraction
-- pass follows that undoes some of the remaining expansion and applies
-- fusion rules that would be immediately counteracted by expansion rules
-- if applied earlier.
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
  Ast.AstMapAccumRDer k bftk eftk f df rf acc0 es ->
    astMapAccumRDer k bftk eftk
                    (expandAstHFun f)
                    (expandAstHFun df)
                    (expandAstHFun rf)
                    (expandAst acc0)
                    (expandAst es)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    astMapAccumLDer k bftk eftk
                    (expandAstHFun f)
                    (expandAstHFun df)
                    (expandAstHFun rf)
                    (expandAst acc0)
                    (expandAst es)
  Ast.AstApply v ll -> astApply (expandAstHFun v) (expandAst ll)
  Ast.AstVar{} -> t
  Ast.AstCond b a2 a3 ->
    astCond (expandAstBool b) (expandAst a2) (expandAst a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = expandAst v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var (expandAst u) (expandAst v)

  Ast.AstPrimalPart v -> astPrimalPart (expandAst v)
  Ast.AstDualPart v -> astDualPart (expandAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (expandAst v)
  Ast.AstFromDual v -> Ast.AstFromDual (expandAst v)

  AstPlusK u v -> expandAst u + expandAst v
  AstTimesK u v -> expandAst u * expandAst v
  Ast.AstN1K NegateOp u -> negate (expandAst u)
  Ast.AstN1K AbsOp u -> abs (expandAst u)
  Ast.AstN1K SignumOp u -> signum (expandAst u)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (expandAst u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (expandAst u) (expandAst v)
  Ast.AstI2K QuotOp u v -> quotH (expandAst u) (expandAst v)
  Ast.AstI2K RemOp u v -> remH (expandAst u) (expandAst v)
  AstConcreteK k -> AstConcreteK k
  Ast.AstFloorK a -> astFloorK (expandAst a)
  Ast.AstFromIntegralK v -> astFromIntegralK $ expandAst v
  Ast.AstCastK v -> astCastK $ expandAst v

  AstPlusS u v -> expandAst u + expandAst v
  AstTimesS u v -> expandAst u * expandAst v
  Ast.AstN1S NegateOp u -> negate (expandAst u)
  Ast.AstN1S AbsOp u -> abs (expandAst u)
  Ast.AstN1S SignumOp u -> signum (expandAst u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (expandAst u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (expandAst u) (expandAst v)
  Ast.AstI2S QuotOp u v -> quotH (expandAst u) (expandAst v)
  Ast.AstI2S RemOp u v -> remH (expandAst u) (expandAst v)
  AstConcreteS a -> AstConcreteS a
  Ast.AstFloorS a -> astFloorS (expandAst a)
  Ast.AstFromIntegralS v -> astFromIntegralS $ expandAst v
  Ast.AstCastS v -> astCastS $ expandAst v

  Ast.AstIndexS shn v ix ->
    astIndexKnobsS (defaultKnobs {knobPhase = PhaseExpansion})
                   shn (expandAst v) (expandAstIxS ix)
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    astScatterS @shm @shn @shp shn (expandAst v) (vars, expandAstIxS ix)
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    astGatherKnobsS @shm @shn @shp
                    (defaultKnobs {knobPhase = PhaseExpansion})
                    shn (expandAst v) (vars, expandAstIxS ix)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (expandAst a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (expandAst a)
  Ast.AstIotaS{} -> t
  Ast.AstAppendS x y -> astAppendS (expandAst x) (expandAst y)
  Ast.AstSliceS i n k v -> astSliceS i n k (expandAst v)
  Ast.AstReverseS v -> astReverseS (expandAst v)
  Ast.AstTransposeS perm v -> {-
   -- disabled until we can reliably fuse back to transpose
   case expandAst v of
    Ast.AstVar{} -> t  -- normal form
    Ast.AstPrimalPart Ast.AstVar{} -> t  -- normal form
    Ast.AstDualPart Ast.AstVar{} -> t  -- normal form
    Ast.AstFromPrimal Ast.AstVar{} -> t  -- normal form
    Ast.AstFromDual Ast.AstVar{} -> t  -- normal form
    Ast.AstProject1{} -> t  -- normal form
    Ast.AstProject2{} -> t  -- normal form
    Ast.AstFromIntegralS{} -> t  -- normal form
    Ast.AstCastS{} -> t  -- normal form
    Ast.AstReplicate{} -> t  -- normal form
      -- TODO: this nf is silly, but right now transposes of replicates
      -- are small arrays and equivalent gathers are large terms and arrays,
      -- so this has to stay. Maybe we should contract gathers back
      -- to transposes of replicates (not only to replicates). Or maybe
      -- we should extend orthotope to any gather schemes, not only
      -- the simple ones.
      -- TODO: review also other nfs here and for AstReshapeS below
    Ast.AstScatterS _ _ (_, ix)
     | gcompare (Permutation.permRank perm) (ixsRank ix) == GGT -> t  -- nf
    Ast.AstSFromR{} -> t  -- normal form
    Ast.AstSFromX{} -> t  -- normal form
    v2 ->  -- not nf, let's express all as a gather
      astTransposeAsGatherS (defaultKnobs {knobExpand = True})
                            perm v2  -- TODO: (normalizePermutation perm)
        -- this is expensive but the only way to guarantee full simplification
    -} astTransposeS perm (expandAst v)
  Ast.AstReshapeS sh v -> {-  -- too hard to fuse back to reshape
   case expandAst v of
    Ast.AstVar{} -> t  -- normal form
    Ast.AstPrimalPart Ast.AstVar{} -> t  -- normal form
    Ast.AstDualPart Ast.AstVar{} -> t  -- normal form
    Ast.AstFromPrimal Ast.AstVar{} -> t  -- normal form
    Ast.AstFromDual Ast.AstVar{} -> t  -- normal form
    Ast.AstProject1{} -> t  -- normal form
    Ast.AstProject2{} -> t  -- normal form
    Ast.AstFromIntegralS{} -> t  -- normal form
    Ast.AstCastS{} -> t  -- normal form
    AstPlusS{} -> t  -- normal form
    AstTimesS{} -> t  -- normal form
    Ast.AstR2S{} -> t  -- normal form
    Ast.AstScatterS{} -> t  -- normal form
    Ast.AstSFromR{} -> t  -- normal form
    Ast.AstSFromX{} -> t  -- normal form
    v2 ->  -- not nf, let's express all as a gather
      astReshapeAsGatherS (defaultKnobs {knobExpand = True})
                          sh v2
        -- this is expensive but the only way to guarantee full simplification
    -} astReshapeS sh (expandAst v)
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
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatmul2S{} -> t

expandAstHFun :: AstSpan s2
              => AstHFun s s2 x y -> AstHFun s s2 x y
expandAstHFun (AstLambda var l) = AstLambda var (expandAst l)

expandAstBool :: AstBool AstMethodLet -> AstBool AstMethodLet
expandAstBool t = case t of
  AstBoolConst{} -> t
  Ast.AstBoolNot arg -> notB $ expandAstBool arg
  Ast.AstBoolAnd arg1 arg2 -> expandAstBool arg1 &&* expandAstBool arg2
  Ast.AstLeqK arg1 arg2 -> expandAst arg1 <=. expandAst arg2
  Ast.AstLeqS arg1 arg2 -> expandAst arg1 <=. expandAst arg2


-- * The simplifying bottom-up pass

simplifyAstInt :: AstInt AstMethodLet -> AstInt AstMethodLet
simplifyAstInt = simplifyAst

simplifyAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
simplifyAstIxS = fmap simplifyAstInt

-- | This function guarantees full simplification (unless redexes are obscured,
-- for which the expansion pass is sometimes a remedy): every redex
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
  Ast.AstMapAccumRDer k bftk eftk f df rf acc0 es ->
    astMapAccumRDer k bftk eftk
                    (simplifyAstHFun f)
                    (simplifyAstHFun df)
                    (simplifyAstHFun rf)
                    (simplifyAst acc0)
                    (simplifyAst es)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    astMapAccumLDer k bftk eftk
                    (simplifyAstHFun f)
                    (simplifyAstHFun df)
                    (simplifyAstHFun rf)
                    (simplifyAst acc0)
                    (simplifyAst es)
  Ast.AstApply v ll -> astApply (simplifyAstHFun v) (simplifyAst ll)
  Ast.AstVar{} -> t
  Ast.AstCond b a2 a3 ->
    astCond (simplifyAstBool b) (simplifyAst a2) (simplifyAst a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = simplifyAst v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var (simplifyAst u) (simplifyAst v)

  Ast.AstPrimalPart v -> astPrimalPart (simplifyAst v)
  Ast.AstDualPart v -> astDualPart (simplifyAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (simplifyAst v)
  Ast.AstFromDual v -> Ast.AstFromDual (simplifyAst v)

  AstPlusK u v -> simplifyAst u + simplifyAst v
  AstTimesK u v -> simplifyAst u * simplifyAst v
  Ast.AstN1K NegateOp u -> negate (simplifyAst u)
  Ast.AstN1K AbsOp u -> abs (simplifyAst u)
  Ast.AstN1K SignumOp u -> signum (simplifyAst u)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (simplifyAst u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2K QuotOp u v -> quotH (simplifyAst u) (simplifyAst v)
  Ast.AstI2K RemOp u v -> remH (simplifyAst u) (simplifyAst v)
  AstConcreteK k -> AstConcreteK k
  Ast.AstFloorK a -> astFloorK (simplifyAst a)
  Ast.AstFromIntegralK v -> astFromIntegralK $ simplifyAst v
  Ast.AstCastK v -> astCastK $ simplifyAst v

  AstPlusS u v -> simplifyAst u + simplifyAst v
  AstTimesS u v -> simplifyAst u * simplifyAst v
  Ast.AstN1S NegateOp u -> negate (simplifyAst u)
  Ast.AstN1S AbsOp u -> abs (simplifyAst u)
  Ast.AstN1S SignumOp u -> signum (simplifyAst u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (simplifyAst u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2S QuotOp u v -> quotH (simplifyAst u) (simplifyAst v)
  Ast.AstI2S RemOp u v -> remH (simplifyAst u) (simplifyAst v)
  AstConcreteS a -> AstConcreteS a
  Ast.AstFloorS a -> astFloorS (simplifyAst a)
  Ast.AstFromIntegralS v -> astFromIntegralS $ simplifyAst v
  Ast.AstCastS v -> astCastS $ simplifyAst v

  Ast.AstIndexS shn v ix ->
    astIndexKnobsS (defaultKnobs {knobPhase = PhaseSimplification})
                   shn (simplifyAst v) (simplifyAstIxS ix)
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    astScatterS @shm @shn @shp shn (simplifyAst v) (vars, simplifyAstIxS ix)
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    astGatherKnobsS @shm @shn @shp
                    (defaultKnobs {knobPhase = PhaseSimplification})
                    shn (simplifyAst v) (vars, simplifyAstIxS ix)
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
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatmul2S{} -> t

simplifyAstHFun :: AstSpan s2
                => AstHFun s s2 x y -> AstHFun s s2 x y
simplifyAstHFun (AstLambda var l) = AstLambda var (simplifyAst l)

simplifyAstBool :: AstBool AstMethodLet -> AstBool AstMethodLet
simplifyAstBool t = case t of
  AstBoolConst{} -> t
  Ast.AstBoolNot arg -> notB $ simplifyAstBool arg
  Ast.AstBoolAnd arg1 arg2 -> simplifyAstBool arg1 &&* simplifyAstBool arg2
  Ast.AstLeqK arg1 arg2 -> simplifyAst arg1 <=. simplifyAst arg2
  Ast.AstLeqS arg1 arg2 -> simplifyAst arg1 <=. simplifyAst arg2

-- * The contraction (e.g., from gather expressions) bottom-up pass

contractAstInt :: AstInt AstMethodLet -> AstInt AstMethodLet
contractAstInt = contractAst

contractAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
contractAstIxS = fmap contractAstInt

-- | When we have multiple backends, there should be one such pass
-- per backend that chooses a representation that is best for the backend.
-- The interpreter would interpret all of the backend-specific term
-- constructors, but the simplifier would ignore all and the user API
-- would not make them available.
--
-- Note that unlike all the other code in this module, this function
-- is not written in a compositional style nor close to it,
-- but it's instead defined in an ad-hoc way based on benchmarks.
contractAst
  :: forall s y. AstSpan s
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
contractAst t0 = case t0 of
  Ast.AstPair t1 t2 -> astPair (contractAst t1) (contractAst t2)
  Ast.AstProject1 v -> astProject1 (contractAst v)
  Ast.AstProject2 v -> astProject2 (contractAst v)
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map contractAst l)
  Ast.AstSum _ (STKS ZSS _) t2 -> astSum0S (contractAst t2)
  Ast.AstSum _ STKScalar t2 -> astFromS STKScalar $ astSum0S (contractAst t2)
  Ast.AstSum
    snat@(SNat @m2)
    stk@(STKS (SNat @n2 :$$ SNat @p2 :$$ ZSS) STKScalar)
    v@(AstTimesS (Ast.AstTransposeS @permt permt
                    (Ast.AstReplicate (SNat @kt) (STKS @sht _ _) t2))
                 (Ast.AstTransposeS @permu permu
                    (Ast.AstReplicate (SNat @ku) (STKS @shu _ _) u2))) ->
    let perm10 = Permutation.makePerm @'[1, 0]
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
        -- (as redundantly spelled out by the casts above) are required
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
  Ast.AstSum n@(SNat @n) (STKS @sh sh _) (AstTimesS t2 u) ->
    let cpermR = backpermCycle $ 1 + sNatValue (shsRank sh)
    in Permutation.permFromList cpermR $ \(cperm :: Permutation.Perm cperm) ->
         gcastWith (unsafeCoerceRefl :: Rank cperm :~: Rank (n : sh)) $
         gcastWith (unsafeCoerceRefl
                    :: Permutation.PermutePrefix cperm (n : sh)
                       :~: sh ++ '[n]) $
         fromMaybe (error "contractAst: impossible non-permutation")
         $ Permutation.permCheckPermutation cperm
         $ astDot1InS sh n (contractAst $ Ast.AstTransposeS cperm t2)
                           (contractAst $ Ast.AstTransposeS cperm u)
  Ast.AstSum snat stk (AstTimesS (Ast.AstLet vart vt t2) u) ->
    {- TODO: do we really need this check?
    | not (varNameInAst vart u) ->
        -- The varNameInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
    -}
    astLet vart
           (contractAst vt)
           (contractAst $ Ast.AstSum snat stk  -- the crucial exposed redex
                                     (AstTimesS t2 u))
  Ast.AstSum snat stk (AstTimesS t2 (Ast.AstLet varu vu u)) ->
    astLet varu
           (contractAst vu)
           (contractAst $ Ast.AstSum snat stk (AstTimesS t2 u))
  Ast.AstSum snat stk (Ast.AstLet var v t2) ->
    astLet var (contractAst v) (contractAst (Ast.AstSum snat stk t2))
  Ast.AstSum snat stk (Ast.AstSum snat2 stk2 (Ast.AstLet var v t2)) ->
    astLet var (contractAst v)
               (contractAst (Ast.AstSum snat stk (Ast.AstSum snat2 stk2 t2)))
  Ast.AstSum snat stk v -> astSum snat stk (contractAst v)
  Ast.AstReplicate snat stk v -> case contractAst v of
    AstConcreteK t -> astConcreteS $ treplicate snat stk $ Concrete t
    AstConcreteS t -> astConcreteS $ treplicate snat stk $ Concrete t
    v2 -> astReplicate snat stk v2
  Ast.AstMapAccumRDer k bftk eftk f df rf acc0 es ->
    astMapAccumRDer k bftk eftk
                    (contractAstHFun f)
                    (contractAstHFun df)
                    (contractAstHFun rf)
                    (contractAst acc0)
                    (contractAst es)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    astMapAccumLDer k bftk eftk
                    (contractAstHFun f)
                    (contractAstHFun df)
                    (contractAstHFun rf)
                    (contractAst acc0)
                    (contractAst es)
  Ast.AstApply v ll -> astApply (contractAstHFun v) (contractAst ll)
  Ast.AstVar{} -> t0
  Ast.AstCond b a2 a3 ->
    astCond (contractAstBool b) (contractAst a2) (contractAst a3)
  -- These are only needed for tests that don't vectorize Ast.
  Ast.AstBuild1 snat (STKS ZSS _)  -- generalize
                (var, Ast.AstSum
                        n _
                        (AstTimesS
                           t2
                           (Ast.AstIndexS _shn
                              u (((:.$) @m (AstIntVar var2) ZIS)))))
    | Just Refl <- testEquality snat (SNat @m)
    , var == var2
    , not (varNameInAst var t2), not (varNameInAst var u) ->
        astDot1InS (snat :$$ ZSS) n
                   (contractAst u)
                   (contractAst
                    $ Ast.AstReplicate snat (ftkToSTK (ftkAst t2)) t2)
  Ast.AstBuild1 snat (STKS ZSS _)
                (var, Ast.AstSum _ _
                        (Ast.AstReshapeS
                           _sh (AstTimesS
                                  t2
                                  (Ast.AstIndexS _shn
                                     u (((:.$) @m (AstIntVar var2) ZIS))))))
    | ftk2@(FTKS (n :$$ ZSS) _) <- ftkAst t2
    , Just Refl <- testEquality snat (SNat @m)
    , var == var2
    , not (varNameInAst var t2), not (varNameInAst var u) ->
        astDot1InS (snat :$$ ZSS) n
                   (contractAst u)
                   (contractAst $ Ast.AstReplicate snat (ftkToSTK ftk2) t2)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = contractAst v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var (contractAst u) (contractAst v)

  Ast.AstPrimalPart v -> astPrimalPart (contractAst v)
  Ast.AstDualPart v -> astDualPart (contractAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (contractAst v)
  Ast.AstFromDual v -> Ast.AstFromDual (contractAst v)

  AstPlusK u v -> contractAst u + contractAst v
  AstTimesK u v -> contractAst u * contractAst v
  Ast.AstN1K NegateOp u -> negate (contractAst u)
  Ast.AstN1K AbsOp u -> abs (contractAst u)
  Ast.AstN1K SignumOp u -> signum (contractAst u)
  Ast.AstR1K RecipOp u -> recip (contractAst u)
  Ast.AstR1K ExpOp u -> exp (contractAst u)
  Ast.AstR1K LogOp u -> log (contractAst u)
  Ast.AstR1K SqrtOp u -> sqrt (contractAst u)
  Ast.AstR1K SinOp u -> sin (contractAst u)
  Ast.AstR1K CosOp u -> cos (contractAst u)
  Ast.AstR1K TanOp u -> tan (contractAst u)
  Ast.AstR1K AsinOp u -> asin (contractAst u)
  Ast.AstR1K AcosOp u -> acos (contractAst u)
  Ast.AstR1K AtanOp u -> atan (contractAst u)
  Ast.AstR1K SinhOp u -> sinh (contractAst u)
  Ast.AstR1K CoshOp u -> cosh (contractAst u)
  Ast.AstR1K TanhOp u -> tanh (contractAst u)
  Ast.AstR1K AsinhOp u -> asinh (contractAst u)
  Ast.AstR1K AcoshOp u -> acosh (contractAst u)
  Ast.AstR1K AtanhOp u -> atanh (contractAst u)
  Ast.AstR2K DivideOp u v -> contractAst u / contractAst v
  Ast.AstR2K PowerOp u v -> contractAst u ** contractAst v
  Ast.AstR2K LogBaseOp u v -> logBase (contractAst u) (contractAst v)
  Ast.AstR2K Atan2Op u v -> atan2H (contractAst u) (contractAst v)
  Ast.AstI2K QuotOp u v -> quotH (contractAst u) (contractAst v)
  Ast.AstI2K RemOp u v -> remH (contractAst u) (contractAst v)
  AstConcreteK k -> AstConcreteK k
  Ast.AstFloorK a -> astFloorK (contractAst a)
  Ast.AstFromIntegralK v -> astFromIntegralK $ contractAst v
  Ast.AstCastK v -> astCastK $ contractAst v

  AstPlusS u v -> contractAst u + contractAst v
  AstTimesS u v -> contractAst u * contractAst v
  Ast.AstN1S NegateOp u -> negate (contractAst u)
  Ast.AstN1S AbsOp u -> abs (contractAst u)
  Ast.AstN1S SignumOp u -> signum (contractAst u)
  Ast.AstR1S RecipOp u -> recip (contractAst u)
  Ast.AstR1S ExpOp u -> exp (contractAst u)
  Ast.AstR1S LogOp u -> log (contractAst u)
  Ast.AstR1S SqrtOp u -> sqrt (contractAst u)
  Ast.AstR1S SinOp u -> sin (contractAst u)
  Ast.AstR1S CosOp u -> cos (contractAst u)
  Ast.AstR1S TanOp u -> tan (contractAst u)
  Ast.AstR1S AsinOp u -> asin (contractAst u)
  Ast.AstR1S AcosOp u -> acos (contractAst u)
  Ast.AstR1S AtanOp u -> atan (contractAst u)
  Ast.AstR1S SinhOp u -> sinh (contractAst u)
  Ast.AstR1S CoshOp u -> cosh (contractAst u)
  Ast.AstR1S TanhOp u -> tanh (contractAst u)
  Ast.AstR1S AsinhOp u -> asinh (contractAst u)
  Ast.AstR1S AcoshOp u -> acosh (contractAst u)
  Ast.AstR1S AtanhOp u -> atanh (contractAst u)
  Ast.AstR2S DivideOp u v -> contractAst u / contractAst v
  Ast.AstR2S PowerOp u v -> contractAst u ** contractAst v
  Ast.AstR2S LogBaseOp u v -> logBase (contractAst u) (contractAst v)
  Ast.AstR2S Atan2Op u v -> atan2H (contractAst u) (contractAst v)
  Ast.AstI2S QuotOp u v -> quotH (contractAst u) (contractAst v)
  Ast.AstI2S RemOp u v -> remH (contractAst u) (contractAst v)
  AstConcreteS a -> AstConcreteS a
  Ast.AstFloorS t -> case contractAst t of
    AstConcreteS a -> astConcreteS (tsfloor $ Concrete a)
    t2 -> astFloorS t2
  Ast.AstFromIntegralS t -> case contractAst t of
    AstConcreteS a -> astConcreteS (tsfromIntegral $ Concrete a)
    t2 -> astFromIntegralS t2
  Ast.AstCastS t -> case contractAst t of
    AstConcreteS a -> astConcreteS (tscast $ Concrete a)
    t2 -> astCastS t2

  Ast.AstIndexS shn v ix ->
    astIndexKnobsS (defaultKnobs {knobPhase = PhaseContraction})
                   shn (contractAst v) (contractAstIxS ix)
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    astScatterS @shm @shn @shp shn (contractAst v) (vars, contractAstIxS ix)
  -- This rule is reverted in vectorization, so contraction phase may be fine.
  Ast.AstGatherS shn v (vars, Ast.AstCond b i1 i2 :.$ prest)
    | not $ any ((`varInAstBool` b) . varNameToAstVarId) (listsToList vars) ->
      contractAst
      $ Ast.AstCond b
                    (Ast.AstGatherS shn v (vars, i1 :.$ prest))
                    (Ast.AstGatherS shn v (vars, i2 :.$ prest))
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    astGatherKnobsS @shm @shn @shp
                    (defaultKnobs {knobPhase = PhaseContraction})
                    shn (contractAst v) (vars, contractAstIxS ix)
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
  Ast.AstIotaS (SNat @n) -> astConcreteS $ tsiota @_ @n
  Ast.AstAppendS x y -> case (contractAst x, contractAst y) of
    (AstConcreteS u, AstConcreteS v) ->
      astConcreteS (tsappend (Concrete u) (Concrete v))
    (x2, y2) -> astAppendS x2 y2
  Ast.AstSliceS i n k t -> case contractAst t of
    AstConcreteS v -> astConcreteS (tsslice i n k $ Concrete v)
    t2 -> astSliceS i n k t2
  Ast.AstReverseS t -> case contractAst t of
    AstConcreteS v -> astConcreteS (tsreverse $ Concrete v)
    t2 -> astReverseS t2
  Ast.AstTransposeS perm v -> astTransposeS perm $ contractAst v  -- TODO:(normalizePermutation perm)
  Ast.AstReshapeS sh2 t -> case contractAst t of
    AstConcreteS v -> astConcreteS (tsreshape sh2 $ Concrete v)
    t2 -> astReshapeS sh2 t2
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
  Ast.AstSum0S{} -> t0
  Ast.AstDot0S{} -> t0
  Ast.AstDot1InS{} -> t0
  Ast.AstMatmul2S{} -> t0

astSum0S :: AstSpan s
         => AstTensor AstMethodLet s (TKS2 sh x)
         -> AstTensor AstMethodLet s (TKS2 '[] x)
astSum0S t = case t of
  Ast.AstSum SNat _ u -> astSum0S u
  Ast.AstReplicate snat (STKS _ STKScalar) u ->
    astSum0S u * (fromPrimal $ AstConcreteS
                  $ Nested.sscalar $ fromInteger $ fromSNat snat)
  Ast.AstReplicate snat STKScalar u ->
    astSFromK u * (fromPrimal $ AstConcreteS
                   $ Nested.sscalar $ fromInteger $ fromSNat snat)
  AstTimesS t1 t2 -> astDot0S t1 t2
  AstConcreteS v ->
    withKnownShS (Nested.sshape v) $
    astConcreteS $ tssum0 (Concrete v)
  Ast.AstFromPrimal u -> Ast.AstFromPrimal $ astSum0S u
  Ast.AstFromDual u -> Ast.AstFromDual $ astSum0S u
  Ast.AstReverseS u -> astSum0S u
  Ast.AstTransposeS _ u -> astSum0S u
  Ast.AstReshapeS _ u -> astSum0S u
  Ast.AstN1S NegateOp u -> negate $ astSum0S u
  Ast.AstSum0S u -> astSum0S u
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS _ _ t1 t2 -> astDot0S t1 t2
  Ast.AstMatmul2S m@SNat SNat p@SNat m1 m2 ->
    astDot0S (astTransposeS (Permutation.makePerm @'[1, 0])
                            (astReplicate p knownSTK m1))
             (astTransposeS (Permutation.makePerm @'[0, 2, 1])
                            (astReplicate m knownSTK m2))
  _ -> Ast.AstSum0S t

astDot0S :: (GoodScalar r, AstSpan s)
         => AstTensor AstMethodLet s (TKS sh r)
         -> AstTensor AstMethodLet s (TKS sh r)
         -> AstTensor AstMethodLet s (TKS '[] r)
astDot0S t1 t2 = case (t1, t2) of
  (Ast.AstReplicate snat STKS{} u1, Ast.AstReplicate _ STKS{} u2) ->
    astDot0S u1 u2 * (fromPrimal $ AstConcreteS
                      $ Nested.sscalar $ fromInteger $ fromSNat snat)
  (Ast.AstReplicate snat STKScalar u1, Ast.AstReplicate _ STKScalar u2) ->
    astSFromK (u1 * u2) * (fromPrimal $ AstConcreteS
                           $ Nested.sscalar $ fromInteger $ fromSNat snat)
  (AstConcreteS v1, AstConcreteS v2) ->
    withKnownShS (Nested.sshape v1) $
    astConcreteS $ tsdot0 (Concrete v1) (Concrete v2)
  (Ast.AstFromPrimal u1, Ast.AstFromPrimal u2) ->
    Ast.AstFromPrimal $ astDot0S u1 u2
  (Ast.AstFromDual u1, Ast.AstFromDual u2) ->
    Ast.AstFromDual $ astDot0S u1 u2
  (Ast.AstTransposeS @_ @sh1 perm1 u1, Ast.AstTransposeS @_ @sh2 perm2 u2)
    | Just Refl <- eqPerm perm1 perm2 ->
      gcastWith (unsafeCoerceRefl :: sh1 :~: sh2) $
      astDot0S u1 u2
  (Ast.AstReverseS u1, Ast.AstReverseS u2) -> astDot0S u1 u2
  (Ast.AstN1S NegateOp u1, Ast.AstN1S NegateOp u2) -> astDot0S u1 u2
  _ -> Ast.AstDot0S t1 t2

astDot1InS :: forall sh n r s. GoodScalar r
           => ShS sh -> SNat n
           -> AstTensor AstMethodLet s (TKS (sh ++ '[n]) r)
           -> AstTensor AstMethodLet s (TKS (sh ++ '[n]) r)
           -> AstTensor AstMethodLet s (TKS sh r)
astDot1InS sh n@SNat t1 t2 = case (t1, t2) of
  (AstConcreteS v1, AstConcreteS v2) ->
    withKnownShS sh $
    astConcreteS $ tsdot1In @_ @sh @n (Concrete v1) (Concrete v2)
  (Ast.AstFromPrimal u1, Ast.AstFromPrimal u2) ->
    Ast.AstFromPrimal $ astDot1InS sh n u1 u2
  (Ast.AstFromDual u1, Ast.AstFromDual u2) ->
    Ast.AstFromDual $ astDot1InS sh n u1 u2
  _ -> Ast.AstDot1InS sh n t1 t2

astMatmul2S :: GoodScalar r
            => SNat m -> SNat n -> SNat p
            -> AstTensor AstMethodLet s (TKS '[m, n] r)
            -> AstTensor AstMethodLet s (TKS '[n, p] r)
            -> AstTensor AstMethodLet s (TKS '[m, p] r)
astMatmul2S m@SNat n@SNat p@SNat t1 t2 = case (t1, t2) of
  (AstConcreteS v1, AstConcreteS v2) ->
    astConcreteS $ tsmatmul2 (Concrete v1) (Concrete v2)
  (Ast.AstFromPrimal u1, Ast.AstFromPrimal u2) ->
    Ast.AstFromPrimal $ astMatmul2S m n p u1 u2
  (Ast.AstFromDual u1, Ast.AstFromDual u2) ->
    Ast.AstFromDual $ astMatmul2S m n p u1 u2
  _ -> Ast.AstMatmul2S m n p t1 t2

attemptMatmul2
  :: forall m n p r s.
     (KnownNat m, KnownNat n, KnownNat p, GoodScalar r, AstSpan s)
  => AstTensor AstMethodLet s (TKS '[m, n] r)
  -> AstTensor AstMethodLet s (TKS '[n, p] r)
  -> Maybe (AstTensor AstMethodLet s (TKS '[m, p] r))
attemptMatmul2 t3 u3 = Just $
  let t4 = contractAst t3
      u4 = contractAst u3
  in case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl ->
      astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl ->
        astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl ->
          astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl ->
            astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
          _ -> case testEquality (typeRep @r) (typeRep @Z0) of
            Just Refl ->
              astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
            _ -> error "attemptMatmul2: unexpected scalar"

contractAstHFun :: AstSpan s2
                => AstHFun s s2 x y -> AstHFun s s2 x y
contractAstHFun (AstLambda var l) = AstLambda var (contractAst l)

contractAstBool :: AstBool AstMethodLet -> AstBool AstMethodLet
contractAstBool t = case t of
  AstBoolConst{} -> t
  Ast.AstBoolNot arg -> notB $ contractAstBool arg
  Ast.AstBoolAnd arg1 arg2 -> contractAstBool arg1 &&* contractAstBool arg2
  Ast.AstLeqK arg1 arg2 -> contractAst arg1 <=. contractAst arg2
  Ast.AstLeqS arg1 arg2 -> contractAst arg1 <=. contractAst arg2


-- * Substitution wrappers

-- | We assume no variable is shared between a binding and its nested binding
-- and nobody substitutes into variables that are bound.
-- This keeps the substitution code simple, because we never need to compare
-- variables to any variable in the bindings.
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

substitute1Ast :: forall s s2 y z. (AstSpan s, AstSpan s2)
               => AstTensor AstMethodLet s2 z -> AstVarName s2 z
               -> AstTensor AstMethodLet s y
               -> Maybe (AstTensor AstMethodLet s y)
substitute1Ast i var = subst where
 subst :: forall s3 y2. AstSpan s3
       => AstTensor AstMethodLet s3 y2
       -> Maybe (AstTensor AstMethodLet s3 y2)
 subst = \case
  Ast.AstPair u v ->
    case (subst u, subst v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) -> Just $ astPair (fromMaybe u mu) (fromMaybe v mv)
  Ast.AstProject1 a -> astProject1 <$> subst a
  Ast.AstProject2 a -> astProject2 <$> subst a
  Ast.AstFromVector snat stk args ->
    let margs = V.map subst args
    in if V.any isJust margs
       then Just $ astFromVector snat stk $ V.zipWith fromMaybe args margs
       else Nothing
  Ast.AstSum snat stk v -> astSum snat stk <$> subst v
  Ast.AstReplicate snat stk v ->
    astReplicate snat stk <$> subst v
  Ast.AstMapAccumRDer k bftk eftk f df rf acc0 es ->
      case ( substitute1AstHFun i var f, substitute1AstHFun i var df
           , substitute1AstHFun i var rf, subst acc0
           , subst es ) of
        (Nothing, Nothing, Nothing, Nothing, Nothing) -> Nothing
        (mf, mdf, mrf, macc0, mes) ->
          Just $ astMapAccumRDer k bftk eftk
                                 (fromMaybe f mf)
                                 (fromMaybe df mdf)
                                 (fromMaybe rf mrf)
                                 (fromMaybe acc0 macc0)
                                 (fromMaybe es mes)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
      case ( substitute1AstHFun i var f, substitute1AstHFun i var df
           , substitute1AstHFun i var rf, subst acc0
           , subst es ) of
        (Nothing, Nothing, Nothing, Nothing, Nothing) -> Nothing
        (mf, mdf, mrf, macc0, mes) ->
          Just $ astMapAccumLDer k bftk eftk
                                 (fromMaybe f mf)
                                 (fromMaybe df mdf)
                                 (fromMaybe rf mrf)
                                 (fromMaybe acc0 macc0)
                                 (fromMaybe es mes)
  Ast.AstApply t ll ->
    case ( substitute1AstHFun i var t
         , subst ll ) of
      (Nothing, Nothing) -> Nothing
      (mt, mll) -> Just $ astApply (fromMaybe t mt) (fromMaybe ll mll)
  Ast.AstVar var2 ->
    if varNameToAstVarId var == varNameToAstVarId var2
    then case sameAstSpan @s3 @s2 of
      Just Refl -> case testEquality var var2 of
        Just Refl -> Just i
        _ -> error $ "substitute1Ast: kind of the variable "
                     ++ show var2 ++ ": " ++ show (varNameToFTK var)
                    ++ ", payload kind: " ++ show (varNameToFTK var2)
                     ++ ", payload: " ++ show i
      _ -> error "substitute1Ast: span"
    else Nothing
  Ast.AstCond b v w ->
    case ( substitute1AstBool i var b
         , subst v
         , subst w ) of
      (Nothing, Nothing, Nothing) -> Nothing
      (mb, mv, mw) ->
        Just $ astCond (fromMaybe b mb) (fromMaybe v mv) (fromMaybe w mw)
  Ast.AstBuild1 k stk (var2, v) ->
    assert (varNameToAstVarId var2 /= varNameToAstVarId var) $
    Ast.AstBuild1 k stk . (var2,) <$> subst v

  Ast.AstLet var2 u v ->
    case (subst u, subst v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) -> Just $ astLet var2 (fromMaybe u mu) (fromMaybe v mv)

  Ast.AstPrimalPart a -> astPrimalPart <$> subst a
  Ast.AstDualPart a -> astDualPart <$> subst a
  Ast.AstFromPrimal a -> Ast.AstFromPrimal <$> subst a
  Ast.AstFromDual a -> Ast.AstFromDual <$> subst a

  AstPlusK u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ fromMaybe u mu + fromMaybe v mv
       else Nothing
  AstTimesK u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ fromMaybe u mu * fromMaybe v mv
       else Nothing
  Ast.AstN1K NegateOp u -> negate <$> subst u
  Ast.AstN1K AbsOp u -> abs <$> subst u
  Ast.AstN1K SignumOp u -> signum <$> subst u
  Ast.AstR1K opCode u -> Ast.AstR1K opCode <$> subst u
  Ast.AstR2K opCode u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ Ast.AstR2K opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstI2K QuotOp u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ quotH (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstI2K RemOp u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ remH (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstConcreteK{} -> Nothing
  Ast.AstFloorK a -> astFloorK <$> subst a
  Ast.AstFromIntegralK v -> astFromIntegralK <$> subst v
  Ast.AstCastK v -> astCastK <$> subst v

  AstPlusS u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ fromMaybe u mu + fromMaybe v mv
       else Nothing
  AstTimesS u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ fromMaybe u mu * fromMaybe v mv
       else Nothing
  Ast.AstN1S NegateOp u -> negate <$> subst u
  Ast.AstN1S AbsOp u -> abs <$> subst u
  Ast.AstN1S SignumOp u -> signum <$> subst u
  Ast.AstR1S opCode u -> Ast.AstR1S opCode <$> subst u
  Ast.AstR2S opCode u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ Ast.AstR2S opCode (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstI2S QuotOp u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ quotH (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstI2S RemOp u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ remH (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstConcreteS{} -> Nothing
  Ast.AstFloorS a -> astFloorS <$> subst a
  Ast.AstFromIntegralS a -> astFromIntegralS <$> subst a
  Ast.AstCastS v -> astCastS <$> subst v

  Ast.AstIndexS shn v ix ->
    case (subst v, substitute1AstIxS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astIndexS shn (fromMaybe v mv) (fromMaybe ix mix)
  Ast.AstScatterS shn v (vars, ix) ->
    case (subst v, substitute1AstIxS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astScatterS shn
                                      (fromMaybe v mv)
                                      (vars, fromMaybe ix mix)
  Ast.AstGatherS shn v (vars, ix) ->
    case (subst v, substitute1AstIxS i var ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astGatherS shn
                                     (fromMaybe v mv)
                                     (vars, fromMaybe ix mix)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS <$> subst a
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS <$> subst a
  Ast.AstIotaS{} -> Nothing
  Ast.AstAppendS x y ->
    case (subst x, subst y) of
      (Nothing, Nothing) -> Nothing
      (mx, my) -> Just $ astAppendS (fromMaybe x mx) (fromMaybe y my)
  Ast.AstSliceS i2 n k v -> astSliceS i2 n k <$> subst v
  Ast.AstReverseS v -> astReverseS <$> subst v
  Ast.AstTransposeS perm v -> astTransposeS perm <$> subst v
  Ast.AstReshapeS sh v -> astReshapeS sh <$> subst v
  Ast.AstZipS v -> Ast.AstZipS <$> subst v
  Ast.AstUnzipS v -> Ast.AstUnzipS <$> subst v
  Ast.AstNestS sh1 sh2 v ->
    astNestS sh1 sh2 <$> subst v
  Ast.AstUnNestS v -> astUnNestS <$> subst v

  Ast.AstFromS stkz v -> astFromS stkz <$> subst v
  Ast.AstSFromK u -> astSFromK <$> subst u
  Ast.AstSFromR sh v -> astSFromR sh <$> subst v
  Ast.AstSFromX sh v -> astSFromX sh <$> subst v

  Ast.AstSum0S v -> astSum0S <$> subst v
  Ast.AstDot0S u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ astDot0S (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstDot1InS sh n u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ astDot1InS sh n (fromMaybe u mu) (fromMaybe v mv)
       else Nothing
  Ast.AstMatmul2S m n p u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ astMatmul2S m n p (fromMaybe u mu) (fromMaybe v mv)
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
  :: forall s s2 s3 x y z.
     AstTensor AstMethodLet s3 z -> AstVarName s3 z -> AstHFun s s2 x y
  -> Maybe (AstHFun s s2 x y)
substitute1AstHFun _i _var AstLambda{} =
  Nothing  -- no outside free variables

substitute1AstBool :: AstSpan s2
                   => AstTensor AstMethodLet s2 y -> AstVarName s2 y
                   -> AstBool AstMethodLet
                   -> Maybe (AstBool AstMethodLet)
substitute1AstBool i var = subst where
 subst :: AstBool AstMethodLet
       -> Maybe (AstBool AstMethodLet)
 subst = \case
  Ast.AstBoolConst{} -> Nothing
  Ast.AstBoolNot arg -> notB <$> subst arg
  Ast.AstBoolAnd arg1 arg2 ->
    let mb1 = subst arg1
        mb2 = subst arg2
    in if isJust mb1 || isJust mb2
       then Just $ fromMaybe arg1 mb1 &&* fromMaybe arg2 mb2
       else Nothing
  Ast.AstLeqK arg1 arg2 ->
    let mr1 = substitute1Ast i var arg1
        mr2 = substitute1Ast i var arg2
    in if isJust mr1 || isJust mr2
       then Just $ fromMaybe arg1 mr1 <=. fromMaybe arg2 mr2
       else Nothing
  Ast.AstLeqS arg1 arg2 ->
    let mr1 = substitute1Ast i var arg1
        mr2 = substitute1Ast i var arg2
    in if isJust mr1 || isJust mr2
       then Just $ fromMaybe arg1 mr1 <=. fromMaybe arg2 mr2
       else Nothing
