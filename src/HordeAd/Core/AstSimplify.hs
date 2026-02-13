{-# LANGUAGE CPP #-}
#if MIN_VERSION_GLASGOW_HASKELL(9,12,1,0)
{-# OPTIONS_GHC -fno-expose-overloaded-unfoldings #-}
#endif
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- {-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
-- {-# OPTIONS_GHC -freduction-depth=10000 #-}
-- {-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | This module holds smart constructors for AST, that is,
-- term-simplifying combinators corresponding to the Ast constructors.
-- The combinators simplify only on the basis of inspecting the roots of their
-- argument term trees. If the arguments get modified,
-- the modified forms are again inspected and potentially simplified again.
--
-- The limited simplification via combinators is enough to uncover redexes
-- for the factorization rules to fire and to undo some of the complication
-- introduced by vectorization. The intention is to leave intact as much
-- as possible of the original terms provided by the user while making
-- sure subterms introduced by vectorization are maximally simplified.
module HordeAd.Core.AstSimplify
  ( RewritePhase(..), SimplifyKnobs (..), defaultKnobs
  , -- * The simplifying combinators, one for almost each AST constructor
    astPair, astProject1, astProject2, astFromVector, astSum, astReplicate
  , astMapAccumLDer, astApply, astCond
  , astConcrete, astConcreteK, astConcreteS

  , astLet

  , astPrimalPart, astDualPart, astPlainPart

  , astFloorK, astFromIntegralK, astCastK, astArgMinK, astArgMaxK

  , astFloorS, astFromIntegralS, astCastS

  , astIndexS, astIndexKnobsS, astScatterS, astGatherS, astGatherKnobsS
  , astAppendS, astSliceS, astReverseS, astTransposeS, astReshapeS

  , astConvert
  , astConvDownKFromS, astConvDownSFromR, astConvDownSFromX
  , astConvUp, astConvUpSFromK, astConvUpRFromS, astConvUpXFromS
  , astIndex0, astSum0, astDot0, astDot1InS, astMatmul2S

    -- * Helper combinators
  , astLetFun
    -- * Substitution operations
  , substituteAst, substituteAstIxS
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Control.Monad (mapAndUnzipM, mplus)
import Data.Foldable qualified as Foldable
import Data.GADT.Compare
import Data.List (findIndex)
import Data.Maybe (catMaybes, fromMaybe, isJust)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Type.Ord (Compare)
import Data.Vector.Generic qualified as V
import Data.Vector.Strict qualified as Data.Vector
import GHC.TypeLits
  ( Nat
  , OrderingI (..)
  , cmpNat
  , sameNat
  , type (+)
  , type (-)
  , type (<=)
  , type (<=?)
  )
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested (Replicate, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert
  (shxFromShS, withShsFromShR, withShsFromShX)
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation (DropLen, Perm (..), TakeLen, permInverse)
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped qualified as Shaped
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types
  (Head, Init, Last, Tail, fromSNat', snatPlus, unsafeCoerceRefl)

import HordeAd.Core.Ast
  ( AstTensor (AstConcreteK, AstConcreteS, AstPlusK, AstPlusS, AstTimesK, AstTimesS)
  )
import HordeAd.Core.Ast hiding (AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersAst (sunReplicate1, sunReplicateN, sunReplicatePrim)
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Conversion
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

data RewritePhase =
    PhaseUnspecified
  | PhaseVectorization
  | PhaseSimplification
  | PhaseExpansion
  | PhaseContraction
 deriving (Show, Eq)

data SimplifyKnobs = SimplifyKnobs
  { knobPhase :: RewritePhase
  }
 deriving Show

defaultKnobs :: SimplifyKnobs
defaultKnobs = SimplifyKnobs PhaseUnspecified

-- @PhaseVectorization@ should only affect the topmost redex.
deVect :: SimplifyKnobs -> SimplifyKnobs
deVect (SimplifyKnobs PhaseVectorization) = SimplifyKnobs PhaseUnspecified
deVect knobs = knobs


-- * Expressing operations as Gather; introduces new variable names

-- | We keep AstTranspose terms for as long as possible, because
-- they are small and fuse nicely in many cases. For some forms of indexing
-- and nesting with reshape and gather they don't fuse, which is when
-- this function is invoked.
astTransposeAsGatherS
  :: forall perm sh s r. KnownSpan s
  => SimplifyKnobs -> Permutation.Perm perm
  -> AstTensor AstMethodLet s (TKS2 sh r)
  -> AstTensor AstMethodLet s (TKS2 (Permutation.PermutePrefix perm sh) r)
{-# NOINLINE astTransposeAsGatherS #-}
astTransposeAsGatherS knobs perm v =
  let FTKS sh _ = ftkAst v
      shn = shsDropLen perm sh
      shp = shsTakeLen perm sh
      shpPermuted = shsPermute perm shp
  in funToVarsIxS @_ @AstMethodLet shpPermuted $ \vars ix ->
    -- See astGatherCase.AstTransposeS for similar code with more comments.
    gcastWith (lemRankMapJust shp) $
    gcastWith (unsafeCoerceRefl :: Rank (TakeLen perm sh) :~: Rank perm) $
    permInverse perm $ \(invperm :: Nested.Perm invperm) proof ->
      case proof (ssxFromShX $ shxFromShS shp) of
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
              !asts = ixsPermutePrefix invperm ix
          in gcastWith (unsafeCoerceRefl
                        :: TakeLen perm sh ++ DropLen perm sh :~: sh) $
             astGatherKnobsS knobs shpPermuted shn shp v (vars, asts)

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
-- in integer arithmetic modulo.
astReshapeAsGatherS
  :: forall sh sh2 x s. KnownSpan s
  => SimplifyKnobs -> ShS sh2 -> AstTensor AstMethodLet s (TKS2 sh x)
  -> AstTensor AstMethodLet s (TKS2 sh2 x)
{-# NOINLINE astReshapeAsGatherS #-}
astReshapeAsGatherS knobs shOut v | Refl <- lemAppNil @sh2
                                  , Refl <- lemAppNil @sh
                                  , FTKS shIn _ <- ftkAst v =
  funToVarsIxS shOut $ \vars ix ->
    let iUnshared :: AstInt AstMethodLet
        iUnshared = ixsToLinear shOut ix
-- This can't be done, because i depends on vars:
--     astLetFun iUnshared $ \i ->
        i = iUnshared  -- sharing broken
        asts :: AstIxS AstMethodLet sh
        !asts = fromLinearIdxS shIn i
    in astGatherKnobsS knobs shOut ZSS shIn v (vars, asts)

-- I can't switch to ixxFromLinear from ox-arrays
-- even just because IntegralH is not available in ox-arrays.
--
-- The inlines are not needed due to function arguments,
-- because there are none, but due to observed significant speedup
-- they provide in tests that intensively use these operations.
-- Maybe specialization doesn't quite work for them? Not verified.
--
-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index.
--
-- If any of the dimensions is 0, the linear index has to be 0
-- (which we can't assert, because j may be a term and so == lies),
-- which is fine, because that's pointing at the start of the empty buffer.
fromLinearIdxS :: forall sh j. IntegralH j
               => ShS sh -> j -> IxS sh j
fromLinearIdxS = \sh lin -> case go sh lin of (# _, ix #) -> ix
  where
    go :: ShS sh1 -> j -> (# j, IxS sh1 j #)
    go ZSS !n = (# n, ZIS #)
    go ((:$$) n sh) lin =
      let (# tensLin, idxInTens #) = go sh lin
          tensLin' = tensLin `quotH` fromIntegral (fromSNat' n)
          i = tensLin `remH` fromIntegral (fromSNat' n)
      in (# tensLin', i :.$ idxInTens #)


-- * The simplifying combinators, one for almost each AST constructor

astPair :: KnownSpan s
        => AstTensor AstMethodLet s x -> AstTensor AstMethodLet s y
        -> AstTensor AstMethodLet s (TKProduct x y)
astPair (Ast.AstProject1 (Ast.AstVar var))
        (Ast.AstProject2 (Ast.AstVar var'))
  | Just Refl <- testEquality var var', var == var' =
    Ast.AstVar var
astPair (Ast.AstPrimalPart (Ast.AstProject1 (Ast.AstVar var)))
        (Ast.AstPrimalPart (Ast.AstProject2 (Ast.AstVar var')))
  | Just Refl <- testEquality var var', var == var' =
    Ast.AstPrimalPart (Ast.AstVar var)
astPair (Ast.AstDualPart (Ast.AstProject1 (Ast.AstVar var)))
        (Ast.AstDualPart (Ast.AstProject2 (Ast.AstVar var')))
  | Just Refl <- testEquality var var', var == var' =
    Ast.AstDualPart (Ast.AstVar var)
astPair (Ast.AstPlainPart (Ast.AstProject1 (Ast.AstVar @s1 var)))
        (Ast.AstPlainPart (Ast.AstProject2 (Ast.AstVar @s2 var')))
  | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2)
  , Just Refl <- testEquality var var', var == var' =
    Ast.AstPlainPart (Ast.AstVar var)
astPair (Ast.AstProject1 (Ast.AstProject1 (Ast.AstVar var)))
        (Ast.AstProject2 (Ast.AstProject1 (Ast.AstVar var')))
  | Just Refl <- testEquality var var', var == var' =
    Ast.AstProject1 (Ast.AstVar var)
astPair (Ast.AstProject1 (Ast.AstProject2 (Ast.AstVar var)))
        (Ast.AstProject2 (Ast.AstProject2 (Ast.AstVar var')))
  | Just Refl <- testEquality var var', var == var' =
    Ast.AstProject2 (Ast.AstVar var)
astPair (Ast.AstFromPrimal v1) (Ast.AstFromPrimal v2) =
  fromPrimal $ astPair v1 v2
astPair (Ast.AstFromDual v1) (Ast.AstFromDual v2) =
  fromDual $ astPair v1 v2
astPair (Ast.AstFromPlain v1) (Ast.AstFromPlain v2) =
  fromPlain $ astPair v1 v2
astPair (AstConvUp ftk1 v1) (AstConvUp ftk2 v2) =
  astConvUp (FTKProduct ftk1 ftk2) (astPair v1 v2)
astPair (AstConvUp ftk1 v1) v2 =
  astConvUp (FTKProduct ftk1 (ftkAst v2)) (astPair v1 v2)
astPair v1 (AstConvUp ftk2 v2) =
  astConvUp (FTKProduct (ftkAst v1) ftk2) (astPair v1 v2)
astPair v1 v2 = Ast.AstPair v1 v2

astProject1
  :: forall x z s. KnownSpan s
  => AstTensor AstMethodLet s (TKProduct x z) -> AstTensor AstMethodLet s x
astProject1 u = case u of
  Ast.AstPair x _z -> x
  Ast.AstFromVector snat (STKProduct stk1 _) v ->
    astFromVector snat stk1 (V.map astProject1 v)
  Ast.AstSum snat (STKProduct stk1 _) x ->
    astSum snat stk1 (astProject1 x)
  Ast.AstReplicate snat (STKProduct stk1 _) x ->
    astReplicate snat stk1 (astProject1 x)
  Ast.AstMapAccumLDer k bftk eftk
                      (AstLambda varf vf)
                      (AstLambda vard vd)
                      (AstLambda varr vr)
                      acc0 es | Nothing <- matchingFTK bftk ftkUnit ->
    let varf2 = varf
        vf2 = astPair (astProject1 vf) (fromPlain $ AstConcreteK Z1)
        vard2 = vard
        vd2 = astPair (astProject1 vd) (fromPlain $ AstConcreteK Z1)
        accftk = ftkAst acc0
        ftkr2 = FTKProduct
                  (adFTK $ FTKProduct accftk ftkUnit)
                  (FTKProduct accftk eftk)
        varr2 = reshapeVarName ftkr2 varr
        astr2 = astVar varr2
        zero = fromPlain $ astConcrete (adFTK bftk) (tdefTarget (adFTK bftk))
        vr2 = substituteAst
                (astPair (astPair (astProject1 (astProject1 astr2))
                                  zero)
                         (astProject2 astr2))
                varr vr
    in Ast.AstProject1
       $ astMapAccumLDer k ftkUnit eftk (AstLambda varf2 vf2)
                                        (AstLambda vard2 vd2)
                                        (AstLambda varr2 vr2) acc0 es
  Ast.AstCond b v1 v2 -> astCond b (astProject1 v1) (astProject1 v2)
  Ast.AstLet var t v -> astLet var t (astProject1 v)
  Ast.AstPrimalPart v -> astPrimalPart $ astProject1 v
  Ast.AstDualPart v -> astDualPart $ astProject1 v
  Ast.AstPlainPart v -> astPlainPart $ astProject1 v
  Ast.AstFromPrimal u1 -> fromPrimal $ astProject1 u1
  Ast.AstFromDual u1 -> fromDual $ astProject1 u1
  Ast.AstFromPlain u1 -> fromPlain $ astProject1 u1
  Ast.AstConvert (ConvT2 c1 _c2) t -> astConvert c1 $ astProject1 t
    -- Even Down conversions are not pushed down projections, so AstConvUp
    -- is not necessary here for consistency of rewriting. The AstConvUp case
    -- commented out below probably doesn't add anything, because ConvCmp is not
    -- a normal form of conversions of products (and ConvZip is ruled out).
    -- AstConvUp (FTKProduct zftk _) t | FTKProduct yftk _ <- ftkAst t ->
    --   astConvert (convUp yftk zftk) (astProject1 t)
  _ -> Ast.AstProject1 u

astProject2
  :: forall x z s. KnownSpan s
  => AstTensor AstMethodLet s (TKProduct x z) -> AstTensor AstMethodLet s z
astProject2 u = case u of
  Ast.AstPair _x z -> z
  Ast.AstFromVector snat (STKProduct _ stk2) v ->
    astFromVector snat stk2 (V.map astProject2 v)
  Ast.AstSum snat (STKProduct _ stk2) x ->
    astSum snat stk2 (astProject2 x)
  Ast.AstReplicate snat (STKProduct _ stk2) x ->
    astReplicate snat stk2 (astProject2 x)
  Ast.AstCond b v1 v2 -> astCond b (astProject2 v1) (astProject2 v2)
  Ast.AstLet var t v -> astLet var t (astProject2 v)
  Ast.AstPrimalPart v -> astPrimalPart $ astProject2 v
  Ast.AstDualPart v -> astDualPart $ astProject2 v
  Ast.AstPlainPart v -> astPlainPart $ astProject2 v
  Ast.AstFromPrimal u1 -> fromPrimal $ astProject2 u1
  Ast.AstFromDual u1 -> fromDual $ astProject2 u1
  Ast.AstFromPlain u1 -> fromPlain $ astProject2 u1
  Ast.AstConvert (ConvT2 _c1 c2) t -> astConvert c2 $ astProject2 t
  _ -> Ast.AstProject2 u

astFromVector :: forall y k s. KnownSpan s
              => SNat k -> SingletonTK y
              -> Data.Vector.Vector (AstTensor AstMethodLet s y)
              -> AstTensor AstMethodLet s (BuildTensorKind k y)
astFromVector (SNat' @1) stk v = astReplicate (SNat @1) stk (v V.! 0)
astFromVector snat@SNat stk l = fromMaybe (Ast.AstFromVector snat stk l) $
  -- This disables some rules, e.g., indexing or summing of fromVector
  -- of concrete arrays, but allocating an extra array of the same size
  -- as the fromVector is not a big deal and early rules are better
  -- then the same rules in contraction phase.
  (case (knownSpan @s, stk) of
     (SPlainSpan, STKScalar) ->
       let unConc :: AstTensor AstMethodLet PlainSpan y
                  -> Maybe (Concrete y)
           unConc (AstConcreteK a) = Just $ Concrete a
           unConc _ = Nothing
       in case V.mapM unConc l of
         Just l4 | V.null l4 -> error "astFromVector: empty vector"
         Just l4 -> Just $ astConcreteS (tfromVector snat stk l4)
         Nothing -> Nothing
     _ -> Nothing)
  `mplus`
  (case (knownSpan @s, stk) of
     (SPlainSpan, STKS _ STKScalar) ->
       let unConc :: AstTensor AstMethodLet PlainSpan y
                  -> Maybe (Concrete y)
           unConc (AstConcreteS a) = Just $ Concrete a
           unConc _ = Nothing
       in case V.mapM unConc l of
         Just l4 | V.null l4 -> error "astFromVector: empty vector"
         Just l4 -> Just $ astConcreteS (tfromVector snat stk l4)
         Nothing -> Nothing
     _ -> Nothing)
  `mplus`
  (let unFromPrimal :: AstTensor AstMethodLet s2 y
                    -> Maybe (AstTensor AstMethodLet (PrimalStepSpan s2) y)
       unFromPrimal (Ast.AstFromPrimal t) = Just t
       unFromPrimal _ = Nothing
   in case V.mapM unFromPrimal l of
     Just l2 | V.null l2 -> error "astFromVector: empty vector"
     Just l2 -> Just $ fromPrimal $ astFromVector snat stk l2
     Nothing -> Nothing)
  `mplus`
  (case knownSpan @s of
     SFullSpan ->
       let unFromDual :: AstTensor AstMethodLet FullSpan y
                      -> Maybe (AstTensor AstMethodLet DualSpan y)
           unFromDual (Ast.AstFromDual t) = Just t
           unFromDual _ = Nothing
       in case V.mapM unFromDual l of
         Just l2 | V.null l2 -> error "astFromVector: empty vector"
         Just l2 -> Just $ fromDual $ astFromVector snat stk l2
         Nothing -> Nothing
     _ -> Nothing)
  `mplus`
  (let unFromPlain :: AstTensor AstMethodLet s2 y
                   -> Maybe (AstTensor AstMethodLet PlainSpan y)
       unFromPlain (Ast.AstFromPlain t) = Just t
       unFromPlain _ = Nothing
   in case V.mapM unFromPlain l of
     Just l2 | V.null l2 -> error "astFromVector: empty vector"
     Just l2 -> Just $ fromPlain $ astFromVector snat stk l2
     Nothing -> Nothing)
  `mplus`
  (let unFrom :: KnownSpan s2
              => FullShapeTK x
              -> AstTensor AstMethodLet s2 y
              -> Maybe (AstTensor AstMethodLet s2 x)
       unFrom yftk (AstConvUp _ t) =
         case matchingFTK (ftkAst t) yftk of
           Just Refl -> Just t
           Nothing -> Nothing  -- e.g., a conversion from X instead of R
       unFrom yftk (Ast.AstFromPrimal t) = fromPrimal <$> unFrom yftk t
       unFrom yftk (Ast.AstFromDual t) = fromDual <$> unFrom yftk t
       unFrom yftk (Ast.AstFromPlain t) = fromPlain <$> unFrom yftk t
       unFrom _ _ = Nothing
   in case V.uncons l of
     Just (Ast.AstConvert c0 t, _) ->
       let yftk = ftkAst t
           -- Here we heavily depend on c being semantically determined
           -- by the domain and codomain. We take an arbitrary such c
           -- and rely on astConvert to replace it with a canonical one.
       in case V.mapM (unFrom yftk) l of
         Just l2 ->
           Just $ astConvert (buildTKConversion snat yftk c0)
                $ astFromVector snat (ftkToSTK yftk) l2
         Nothing -> Nothing
     Just (Ast.AstFromPrimal (Ast.AstConvert c0 t), _) ->
       let yftk = ftkAst t
       in case V.mapM (unFrom yftk) l of
         Just l2 ->
           Just $ astConvert (buildTKConversion snat yftk c0)
                $ astFromVector snat (ftkToSTK yftk) l2
         Nothing -> Nothing
     Just (Ast.AstFromDual (Ast.AstConvert c0 t), _) ->
       let yftk = ftkAst t
       in case V.mapM (unFrom yftk) l of
         Just l2 ->
           Just $ astConvert (buildTKConversion snat yftk c0)
                $ astFromVector snat (ftkToSTK yftk) l2
         Nothing -> Nothing
     Just (Ast.AstFromPlain (Ast.AstConvert c0 t), _) ->
       let yftk = ftkAst t
       in case V.mapM (unFrom yftk) l of
         Just l2 ->
           Just $ astConvert (buildTKConversion snat yftk c0)
                $ astFromVector snat (ftkToSTK yftk) l2
         Nothing -> Nothing
     Just{} -> Nothing
     Nothing -> error "astFromVector: empty vector")
  `mplus`
  (let unFrom :: KnownSpan s2
              => AstTensor AstMethodLet s2 (TKS '[] r)
              -> Maybe (AstTensor AstMethodLet s2 (TKScalar r))
       unFrom (AstConvUpSFromK t) = Just t
         -- AstConvUp above subsumes AstConvUpSFromK, but the cases below
         -- can be easily handled only within this narrow typing.
         -- The AstConcreteS is impossible for R and X, so a generalization
         -- to RFromK or XFromK is not worth the effort.
       unFrom (AstConcreteS v) = Just $ AstConcreteK $ Nested.sunScalar v
       unFrom (Ast.AstSum snat2 (STKS _ STKScalar) v) =
         Just $ astSum snat2 STKScalar v
       unFrom (Ast.AstFromPrimal t) = fromPrimal <$> unFrom t
       unFrom (Ast.AstFromDual t) = fromDual <$> unFrom t
       unFrom (Ast.AstFromPlain t) = fromPlain <$> unFrom t
       unFrom _ = Nothing
   in case ftkAst . fst <$> V.uncons l of
     Just (FTKS ZSS FTKScalar) ->
       case V.mapM unFrom l of
         Just l2 -> Just $ astFromVector snat STKScalar l2
         Nothing -> Nothing
     Just _ -> Nothing
     Nothing -> error "astFromVector: empty vector")

astSum :: forall y k s. (KnownSpan s, TKAllNum y)
       => SNat k -> SingletonTK y
       -> AstTensor AstMethodLet s (BuildTensorKind k y)
       -> AstTensor AstMethodLet s y
astSum snat@SNat stk t0 = case t0 of
  _ | Just Refl <- testEquality snat (SNat @0) ->
      let ftk = razeFTK snat stk (ftkAst t0)
      in fromPlain $ astConcrete ftk (tdefTarget ftk)
  {- TODO: this results in small PP terms, but much higher allocation somewhere:
  _ | STKS ZSS STKScalar <- stk ->
      sfromK $ astSum snat STKScalar t0 -}
  _ | STKS sh (STKScalar @r) <- stk
    , Just u <- unRepl1 t0
    , Dict0 <- numFromTKAllNum (Proxy @r) ->
      u * (fromPlain $ AstConcreteS @r
           $ Nested.sreplicatePrim sh $ fromIntegral $ fromSNat' snat)
  -- This exchanges one multiplication at rank n+1 for two multiplications
  -- at rank n, which should be faster. We choose t1, since it's likely to be
  -- concrete and so it's easier to see if it's replicated and also t2 is
  -- likely to be AstTimes, to be processed recusively. This rule may distrupt
  -- recognizing matmul, sdot1In, etc., but it sometimes leads to a smaller
  -- and better sdot1In.
  AstTimesS t1 t2
    | STKS _sh (STKScalar @r) <- stk
    , Just u <- unRepl1 t1
    , Dict0 <- numFromTKAllNum (Proxy @r) ->
      u * astSum snat stk t2
  AstConcreteS @_ @sh2 t -> case stk of
    STKS @sh _ STKScalar ->
      gcastWith (unsafeCoerceRefl :: k ': sh :~: sh2) $
      astConcreteS $ tsum snat stk $ Concrete t
    STKScalar ->
      gcastWith (unsafeCoerceRefl :: '[k] :~: sh2) $
      astConcreteK $ tsum snat stk $ Concrete t
  Ast.AstIotaS @_ @r n ->
    let i :: r
        i = fromIntegral $ fromSNat' n * (fromSNat' n - 1) `div` 2
    in case stk of
      STKScalar -> AstConcreteK $ i
      STKS ZSS STKScalar -> AstConcreteS $ Nested.sscalar i
  Ast.AstReverseS v -> astSum snat stk v
  _ | Just Refl <- testEquality snat (SNat @1)
    , STKScalar <- stk ->
      astConvDownKFromS $ astIndexS ZSS t0 (0 :.$ ZIS)
  _ | Just Refl <- testEquality snat (SNat @1)
    , STKS sh _  <- stk ->  -- other cases too rare
      astIndexS sh t0 (0 :.$ ZIS)  -- astReshape slows down the CNNO test
  Ast.AstFromVector _ stk2 l ->
    case stk of
      STKScalar @r | Dict0 <- numFromTKAllNum (Proxy @r) ->
        case stk2 of
          STKScalar -> foldr1 (+) l
          STKS ZSS STKScalar -> kfromS $ foldr1 (+) l
      STKR _ (STKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r)
                            , STKR{} <- stk2 ->
        foldr1 (+) l
      STKS _ (STKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) ->
        case stk2 of
          STKScalar -> sfromK $ foldr1 (+) l
          STKS{} -> foldr1 (+) l
      STKX _ (STKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r)
                            , STKX{} <- stk2 ->
        foldr1 (+) l
      _ -> Ast.AstSum snat stk t0
  -- See the analogous astSliceS rule.
  Ast.AstTransposeS (SNat' @1 `PCons` SNat' @0 `PCons` PNil) t
    | FTKS (_ :$$ _ :$$ _) _ <- ftkAst t
    , STKS (snat1 :$$ sh3) x <- stk
    , Just u <- unRepl1 t ->
      astReplicate snat1 (STKS sh3 x)
      $ astSum snat (STKS sh3 x) u
  Ast.AstReplicate _ STKScalar v | STKScalar @r <- stk
                                 , Dict0 <- numFromTKAllNum (Proxy @r) ->
    v * fromPlain (AstConcreteK $ fromIntegral $ fromSNat' snat)
  Ast.AstReplicate _ STKS{} v | STKS sh (STKScalar @r) <- stk
                              , Dict0 <- numFromTKAllNum (Proxy @r) ->
    v * (fromPlain $ AstConcreteS @r
         $ Nested.sreplicatePrim sh $ fromIntegral $ fromSNat' snat)
  Ast.AstReplicate _ _ v | STKR _ (STKScalar @r) <- stk
                         , Dict0 <- numFromTKAllNum (Proxy @r) ->
    case ftkAst v of
      FTKR sh' FTKScalar ->
        withShsFromShR sh' $ \(sh :: ShS sh) ->
          v * astConvUpRFromS sh'
                (fromPlain $ AstConcreteS @r
                 $ Nested.sreplicatePrim sh $ fromIntegral $ fromSNat' snat)
  Ast.AstReplicate _ _ v | STKX _ (STKScalar @r) <- stk
                         , Dict0 <- numFromTKAllNum (Proxy @r) ->
    case ftkAst v of
      FTKX sh' FTKScalar ->
        withShsFromShX sh' $ \(sh :: ShS sh) ->
          v * astConvUpXFromS sh'
                (fromPlain $ AstConcreteS @r
                 $ Nested.sreplicatePrim sh $ fromIntegral $ fromSNat' snat)
  -- This keeps tensors alive for longer, but it enables new simplifications,
  -- while hiding a sum inside let not often prevents other simplifications,
  -- because there are few redexes with sum but not at the top.
  Ast.AstLet var u v -> astLet var u (astSum snat stk v)
  Ast.AstFromPrimal v -> fromPrimal $ astSum snat stk v
  Ast.AstFromDual v -> fromDual $ astSum snat stk v
  Ast.AstFromPlain v -> fromPlain $ astSum snat stk v
  Ast.AstScatterS shm shn shp v (vars, (:.$) @k2 i1 rest)
    | STKS{} <- stk ->
      -- This boolean term may have free variables that act as universally
      -- quantified.
      case 0 <=. i1 &&* i1 <=. valueOf @k2 - 1 of
        AstConcreteK True ->
          astScatterS shm shn (shsTail shp) v (vars, rest)
        _ -> Ast.AstSum snat stk t0
  AstConvUp @xs zftk t ->
    let xftk = ftkAst t
        c = convUp xftk zftk
        zftkRazed = razeFTK snat stk zftk
    in case razeSTK zftkRazed (ftkToSTK xftk) of
      (xstkRazed :: SingletonTK x) ->
        gcastWith (unsafeCoerceRefl :: BuildTensorKind k x :~: xs) $
        case lemTKAllNumBuild snat stk of
          Dict0 -> case lemTKAllNumBackConvert c of
            Dict0 -> case lemTKAllNumRaze snat xstkRazed of
              Dict0 ->
                astConvUp zftkRazed (astSum snat xstkRazed t)
                  -- this uses razed c, not c
  _ -> Ast.AstSum snat stk t0

astReplicate :: forall y k s. KnownSpan s
             => SNat k -> SingletonTK y
             -> AstTensor AstMethodLet s y
             -> AstTensor AstMethodLet s (BuildTensorKind k y)
astReplicate snat@SNat stk t0 = case t0 of
  Ast.AstPair t1 t2 | STKProduct stk1 stk2 <- stk ->
    astPair (astReplicate snat stk1 t1) (astReplicate snat stk2 t2)
  -- This doesn't prevent indexing of replicate, because indexing goes inside
  -- the conditional, but it prevents the sum(replicate(cond)) simplification,
  -- because sum can't go inside, because it's costly and cond is eager.
  -- Ast.AstCond b v1 v2 ->
  --  astCond b (astReplicate snat stk v1) (astReplicate snat stk v2)
  -- TODO: This rules is, in principle, very good, because it permits many other
  -- rules to fire. However, one of these other rules is indexing of transpose
  -- that in some cases complicates terms and causes OOM in CNNI tests.
  -- We need to restrict the indexing rule more effectively first.
  -- Ast.AstLet var t v -> astLet var t (astReplicate snat stk v)
  Ast.AstFromPrimal v -> fromPrimal $ astReplicate snat stk v
  Ast.AstFromDual v -> fromDual $ astReplicate snat stk v
  Ast.AstFromPlain v -> fromPlain $ astReplicate snat stk v
  AstConcreteK t | fromSNat' snat < 100 ->  -- likely not to be O(data size)
    astConcreteS $ treplicate snat stk $ Concrete t
  AstConcreteS t | fromSNat' snat < 100 ->  -- tough trade-offs here
    astConcreteS $ treplicate snat stk $ Concrete t
      -- revisit the trade-offs once we compile instead of interpreting
      -- and so building big blobby concrete arrays is cheap
  AstConvUp zftk t ->
    let xftk = ftkAst t
    in astConvUp (buildFTK snat zftk) (astReplicate snat (ftkToSTK xftk) t)
  _ -> Ast.AstReplicate snat stk t0
  -- TODO: maybe add a rule and then generalize:
  -- replicate n1 (str (replicate n2 u))
  -- ~> transpose [0, 2, 1] (replicate n1 (replicate n2 u))
  -- but the reverse rule is already in astTransposeS

astMapAccumLDer
  :: forall accy by ey k s. KnownSpan s
  => SNat k
  -> FullShapeTK by
  -> FullShapeTK ey
  -> AstHFun s
             (TKProduct accy ey) (TKProduct accy by)
  -> AstHFun s
             (TKProduct (ADTensorKind (TKProduct accy ey))
                        (TKProduct accy ey))
             (ADTensorKind (TKProduct accy by))
  -> AstHFun s
             (TKProduct (ADTensorKind (TKProduct accy by))
                        (TKProduct accy ey))
             (ADTensorKind (TKProduct accy ey))
  -> AstTensor AstMethodLet s accy
  -> AstTensor AstMethodLet s (BuildTensorKind k ey)
  -> AstTensor AstMethodLet s (TKProduct accy (BuildTensorKind k by))
astMapAccumLDer k bftk eftk (AstLambda varf vf)
                            (AstLambda vard vd)
                            (AstLambda varr vr)
                (AstConvUp @accyFrom accftk acc0From) es =
  let accftkFrom = ftkAst acc0From
      accFromSTK = ftkToSTK accftkFrom
      ftkf2 = FTKProduct accftkFrom eftk
      varf2 = reshapeVarName ftkf2 varf
      astf2 = astVar varf2
      vf2 =
        let subbed =
              substituteAst
                (astPair (astConvUp @accyFrom accftk (astProject1 astf2))
                         (astProject2 astf2))
                varf vf
        in astConvDown @(TKProduct accy by)
                     (STKProduct accFromSTK (ftkToSTK bftk))
                     subbed
      ftkd2 = FTKProduct
                (adFTK $ FTKProduct accftkFrom eftk)
                (FTKProduct accftkFrom eftk)
      vard2 = reshapeVarName ftkd2 vard
      astd2 = astVar vard2
      vd2 =
        let subbed =
              substituteAst
                (astPair (astPair (astConvUp @(ADTensorKind accyFrom)
                                     (adFTK accftk)
                                     (astProject1 (astProject1 astd2)))
                                  (astProject2 (astProject1 astd2)))
                         (astPair (astConvUp @accyFrom accftk
                                     (astProject1 (astProject2 astd2)))
                                  (astProject2 (astProject2 astd2))))
                vard vd
        in astConvDown @(ADTensorKind (TKProduct accy by))
                     (adSTK $ STKProduct accFromSTK (ftkToSTK bftk))
                     subbed
      ftkr2 = FTKProduct
                (adFTK $ FTKProduct accftkFrom bftk)
                (FTKProduct accftkFrom eftk)
      varr2 = reshapeVarName ftkr2 varr
      astr2 = astVar varr2
      vr2 =
        let subbed =
              substituteAst
                (astPair (astPair (astConvUp @(ADTensorKind accyFrom)
                                     (adFTK accftk)
                                     (astProject1 (astProject1 astr2)))
                                  (astProject2 (astProject1 astr2)))
                         (astPair (astConvUp @accyFrom accftk
                                     (astProject1 (astProject2 astr2)))
                                  (astProject2 (astProject2 astr2))))
                varr vr
        in astConvDown @(ADTensorKind (TKProduct accy ey))
                     (adSTK $ STKProduct accFromSTK (ftkToSTK eftk))
                     subbed
  in astConvUp @(TKProduct accyFrom (BuildTensorKind k by))
               (FTKProduct accftk (buildFTK k bftk))
     $ astMapAccumLDer k bftk eftk (AstLambda varf2 vf2)
                                   (AstLambda vard2 vd2)
                                   (AstLambda varr2 vr2)
                                   acc0From es
astMapAccumLDer k bftk eftk (AstLambda varf vf)
                            (AstLambda vard vd)
                            (AstLambda varr vr)
                acc0 (AstConvUp @esShsFrom _esShsFTK esFrom) =
  let accftk = ftkAst acc0
      accstk = ftkToSTK accftk
      esShsFrom = ftkAst esFrom
      esShsFromSTK = ftkToSTK esShsFrom
  in case razeSTK eftk esShsFromSTK of
    (eftkFromSTK :: SingletonTK eyFrom) ->
      gcastWith (unsafeCoerceRefl :: BuildTensorKind k eyFrom :~: esShsFrom) $
      let eftkFrom = razeFTK k eftkFromSTK esShsFrom
          ftkf2 = FTKProduct accftk eftkFrom
          varf2 = reshapeVarName ftkf2 varf
          astf2 = astVar varf2
          vf2 =
            let subbed =
                  substituteAst
                    (astPair (astProject1 astf2)
                             (astConvUp @eyFrom eftk (astProject2 astf2)))
                    varf vf
            in subbed
          ftkd2 = FTKProduct
                    (adFTK $ FTKProduct accftk eftkFrom)
                    (FTKProduct accftk eftkFrom)
          vard2 = reshapeVarName ftkd2 vard
          astd2 = astVar vard2
          vd2 =
            let subbed =
                  substituteAst
                    (astPair (astPair (astProject1 (astProject1 astd2))
                                      (astConvUp @(ADTensorKind eyFrom)
                                         (adFTK eftk)
                                         (astProject2 (astProject1 astd2))))
                             (astPair (astProject1 (astProject2 astd2))
                                      (astConvUp @eyFrom eftk
                                         (astProject2 (astProject2 astd2)))))
                    vard vd
            in subbed
          ftkr2 = FTKProduct
                    (adFTK $ FTKProduct accftk bftk)
                    (FTKProduct accftk eftkFrom)
          varr2 = reshapeVarName ftkr2 varr
          astr2 = astVar varr2
          vr2 =
            let subbed =
                  substituteAst
                    (astPair (astProject1 astr2)
                             (astPair (astProject1 (astProject2 astr2))
                                      (astConvUp @eyFrom eftk
                                         (astProject2 (astProject2 astr2)))))
                    varr vr
            in astConvDown @(ADTensorKind (TKProduct accy ey))
                         (adSTK $ STKProduct accstk eftkFromSTK)
                         subbed
      in astMapAccumLDer k bftk eftkFrom (AstLambda varf2 vf2)
                                         (AstLambda vard2 vd2)
                                         (AstLambda varr2 vr2)
                                         acc0 esFrom
astMapAccumLDer k bftk eftk f df rf acc0 es =
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es

astApply :: forall x z s. KnownSpan s
         => AstHFun s x z -> AstTensor AstMethodLet s x
         -> AstTensor AstMethodLet s z
astApply (AstLambda !var !v) u = astLet var u v

astCond :: KnownSpan s
        => AstBool AstMethodLet
        -> AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
        -> AstTensor AstMethodLet s y
astCond (AstConcreteK b) v w = if b then v else w
astCond (Ast.AstBoolNotK b) v w = astCond b w v
astCond b (Ast.AstFromPrimal v) (Ast.AstFromPrimal w) =
  fromPrimal $ astCond b v w
astCond b (Ast.AstFromDual v) (Ast.AstFromDual w) =
  fromDual $ astCond b v w
astCond b (Ast.AstFromPlain v) (Ast.AstFromPlain w) =
  fromPlain $ astCond b v w
-- We rely here on c and the other conversion being semantically equal.
astCond b (AstConvUp zftk v) (AstConvUp _ w)
  | Just Refl <- matchingFTK (ftkAst v) (ftkAst w) =
    astConvUp zftk $ astCond b v w
astCond b v w = Ast.AstCond b v w

-- Invariant: if the variable has bounds, the expression can only have
-- values within the bounds (regardless of what the `bounds` call would say).
astLet :: forall y z s s2. KnownSpan s2
       => AstVarName '(s, y) -> AstTensor AstMethodLet s y
       -> AstTensor AstMethodLet s2 z
       -> AstTensor AstMethodLet s2 z
astLet _var _u v@Ast.AstConcreteK{} = v
astLet _var _u v@Ast.AstConcreteS{} = v
astLet _var _u v@Ast.AstIotaS{} = v
astLet var u v@(Ast.AstVar var2) =
  if varNameToAstVarId var2 == varNameToAstVarId var
  then case testEquality var var2 of
    Just Refl -> u
    _ -> error "astLet: wrong variable types at AstVar"
  else v
astLet var u v@(Ast.AstPrimalPart (Ast.AstVar var2)) =  -- a common noop
  if varNameToAstVarId var2 == varNameToAstVarId var
  then case testEquality var var2 of
    Just Refl -> astPrimalPart u
    _ -> error "astLet: wrong variable types at AstPrimalPart"
  else v
astLet var u v@(Ast.AstDualPart (Ast.AstVar var2)) =  -- a noop
  if varNameToAstVarId var2 == varNameToAstVarId var
  then case testEquality var var2 of
    Just Refl -> astDualPart u
    _ -> error "astLet: wrong variable types at AstDualPart"
  else v
astLet var u v@(Ast.AstPlainPart (Ast.AstVar var2)) =  -- a noop
  if varNameToAstVarId var2 == varNameToAstVarId var
  then case testEquality var var2 of
    Just Refl -> astPlainPart u
    _ -> error "astLet: wrong variable types at AstPlainPart"
  else v
astLet var u v | astIsSmall True u =
  substituteAst u var v
astLet var u (Ast.AstFromPrimal v0) = fromPrimal $ astLet var u v0
astLet var u (Ast.AstFromDual v0) = fromDual $ astLet var u v0
astLet var u (Ast.AstFromPlain v0) = fromPlain $ astLet var u v0
astLet var (Ast.AstFromPrimal u) v =
  withKnownSpan (varNameToSpan var)
  $ astLetFun u $ \ !ast1 -> substituteAst (fromPrimal ast1) var v
astLet var (Ast.AstFromDual u) v =
  astLetFun u $ \ !ast1 -> substituteAst (fromDual ast1) var v
astLet var (Ast.AstFromPlain u) v =
  withKnownSpan (varNameToSpan var)
  $ astLetFun u $ \ !ast1 -> substituteAst (fromPlain ast1) var v
astLet var (Ast.AstPair u1 u2) v =
  withKnownSpan (varNameToSpan var)
  $ astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
      substituteAst (Ast.AstPair ast1 ast2) var v
astLet var (Ast.AstLet varN uN (Ast.AstPair u1 u2)) v =
  astLet varN uN
  $ withKnownSpan (varNameToSpan var)
  $ astLetFun u1 $ \ !ast1 -> astLetFun u2 $ \ !ast2 ->
      substituteAst (Ast.AstPair ast1 ast2) var v
-- This is a common case, e.g., from representing conditionals.
astLet var (Ast.AstFromVector snat stk u) v | V.length u == 2 =
  withKnownSpan (varNameToSpan var)
  $ astLetFun (u V.! 0) $ \ !ast1 -> astLetFun (u V.! 1) $ \ !ast2 ->
      substituteAst (Ast.AstFromVector snat stk
                     $ V.fromListN 2 [ast1, ast2]) var v
astLet var (Ast.AstLet varN uN
              (Ast.AstFromVector snat stk u)) v | V.length u == 2 =
  astLet varN uN
  $ withKnownSpan (varNameToSpan var)
  $ astLetFun (u V.! 0) $ \ !ast1 -> astLetFun (u V.! 1) $ \ !ast2 ->
      substituteAst (Ast.AstFromVector snat stk
                     $ V.fromListN 2 [ast1, ast2]) var v
astLet var (Ast.AstReplicate snat stk a) v =
  let var2 = reshapeVarName (ftkAst a) var
      ast = Ast.AstReplicate snat stk $ astVar var2
  in astLet var2 a (substituteAst ast var v)
astLet var (Ast.AstTransposeS perm a) v =
  let var2 = reshapeVarName (ftkAst a) var
      ast = Ast.AstTransposeS perm $ astVar var2
  in astLet var2 a (substituteAst ast var v)
astLet var (Ast.AstConvert c a) v
  | checkAstConvUp c a =
    let var2 = reshapeVarName (ftkAst a) var
        ast = withKnownSpan (varNameToSpan var) $ astConvert c $ astVar var2
    in astLet var2 a (substituteAst ast var v)
astLet var u (Ast.AstConvert c a)
  | checkAstConvUp c a =
    astConvert c $ astLet var u a
astLet var u v = Ast.AstLet var u v

astPrimalPart :: KnownSpan s
              => AstTensor AstMethodLet s y
              -> AstTensor AstMethodLet (PrimalStepSpan s) y
astPrimalPart t = case t of
  Ast.AstPair t1 t2 -> astPair (astPrimalPart t1) (astPrimalPart t2)
  -- We really need equality saturation...
  Ast.AstProject1 u@Ast.AstMapAccumLDer{} -> astProject1 $ astPrimalPart u
  Ast.AstProject2 u@Ast.AstMapAccumLDer{} -> astProject2 $ astPrimalPart u
  Ast.AstProject1 u@(Ast.AstProject1 Ast.AstMapAccumLDer{}) ->
    astProject1 $ astPrimalPart u
  Ast.AstProject1 u@(Ast.AstProject2 Ast.AstMapAccumLDer{}) ->
    astProject1 $ astPrimalPart u
  Ast.AstProject2 u@(Ast.AstProject2 Ast.AstMapAccumLDer{}) ->
    astProject2 $ astPrimalPart u
  Ast.AstProject2 u@(Ast.AstProject1 Ast.AstMapAccumLDer{}) ->
    astProject2 $ astPrimalPart u
  Ast.AstProject1{} -> Ast.AstPrimalPart t
  Ast.AstProject2{} -> Ast.AstPrimalPart t
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map astPrimalPart l)
  Ast.AstSum snat stk v ->
    astSum snat stk (astPrimalPart v)
  Ast.AstReplicate snat stk v ->
    astReplicate snat stk (astPrimalPart v)
  Ast.AstMapAccumLDer k bftk eftk (AstLambda varf vf)
                                  (AstLambda vard vd)
                                  (AstLambda varr vr) acc0 es ->
    let varf2 = respanVarName varf
        astf2 = fromPrimal $ astVar varf2
        vf2 = astPrimalPart $ substituteAst astf2 varf vf
        vard2 = respanVarName vard
        astd2 = fromPrimal $ astVar vard2
        vd2 = astPrimalPart $ substituteAst astd2 vard vd
        varr2 = respanVarName varr
        astr2 = fromPrimal $ astVar varr2
        vr2 = astPrimalPart $ substituteAst astr2 varr vr
    in astMapAccumLDer k bftk eftk (AstLambda varf2 vf2)
                                   (AstLambda vard2 vd2)
                                   (AstLambda varr2 vr2)
                       (astPrimalPart acc0) (astPrimalPart es)
  Ast.AstApply{} -> Ast.AstPrimalPart t
  Ast.AstVar{} -> Ast.AstPrimalPart t  -- the only normal form
  Ast.AstCond b a2 a3 -> astCond b (astPrimalPart a2) (astPrimalPart a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = astPrimalPart v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var u (astPrimalPart v)

  Ast.AstPrimalPart{} -> Ast.AstPrimalPart t
  Ast.AstDualPart{} -> Ast.AstPrimalPart t
  Ast.AstPlainPart{} -> Ast.AstPrimalPart t  -- impossible, but fine
  Ast.AstFromPrimal v -> v
  Ast.AstFromDual v ->
    let ftk = ftkAst v
    in fromPlain $ astConcrete ftk (tdefTarget ftk)
  Ast.AstFromPlain v -> fromPlain v

  AstPlusK u v -> astPrimalPart u + astPrimalPart v
  AstTimesK u v -> astPrimalPart u * astPrimalPart v
  Ast.AstN1K NegateOp u -> negate (astPrimalPart u)
  Ast.AstN1K AbsOp u -> abs (astPrimalPart u)
  Ast.AstN1K SignumOp u -> signum (astPrimalPart u)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (astPrimalPart u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2K QuotOp u v -> quotH (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2K RemOp u v -> remH (astPrimalPart u) (astPrimalPart v)
  AstConcreteK{} -> Ast.AstPrimalPart t
  Ast.AstFloorK{} -> Ast.AstPrimalPart t
  Ast.AstFromIntegralK{} -> Ast.AstPrimalPart t
  Ast.AstCastK v -> astCastK $ astPrimalPart v
  Ast.AstArgMinK{} -> Ast.AstPrimalPart t
  Ast.AstArgMaxK{} -> Ast.AstPrimalPart t

  AstPlusS u v -> astPrimalPart u + astPrimalPart v
  AstTimesS u v -> astPrimalPart u * astPrimalPart v
  Ast.AstN1S NegateOp u -> negate (astPrimalPart u)
  Ast.AstN1S AbsOp u -> abs (astPrimalPart u)
  Ast.AstN1S SignumOp u -> signum (astPrimalPart u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astPrimalPart u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2S QuotOp u v -> quotH (astPrimalPart u) (astPrimalPart v)
  Ast.AstI2S RemOp u v -> remH (astPrimalPart u) (astPrimalPart v)
  AstConcreteS{} -> Ast.AstPrimalPart t
  Ast.AstFloorS{} -> Ast.AstPrimalPart t
  Ast.AstFromIntegralS{} -> Ast.AstPrimalPart t
  Ast.AstCastS v -> astCastS $ astPrimalPart v
  Ast.AstArgMinS{} -> Ast.AstPrimalPart t
  Ast.AstArgMaxS{} -> Ast.AstPrimalPart t

  Ast.AstIndexS shn v ix ->
    astIndexS shn (astPrimalPart v) ix
  Ast.AstScatterS shm shn shp v (vars, ix) ->
    astScatterS shm shn shp (astPrimalPart v) (vars, ix)
  Ast.AstGatherS shm shn shp v (vars, ix) ->
    astGatherS shm shn shp (astPrimalPart v) (vars, ix)
  Ast.AstIotaS{} -> Ast.AstPrimalPart t
  Ast.AstAppendS x y -> astAppendS (astPrimalPart x) (astPrimalPart y)
  Ast.AstSliceS i n k v -> astSliceS i n k (astPrimalPart v)
  Ast.AstReverseS v -> astReverseS (astPrimalPart v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astPrimalPart v)
  Ast.AstReshapeS sh v -> astReshapeS sh (astPrimalPart v)

  -- Most conversions need to stay down here to cancel out.
  Ast.AstConvert c a ->
    if checkAstConvUp c a
    then astConvert c $ astPrimalPart a
    else Ast.AstPrimalPart t

  -- These should not appear in this context unless via wacky tests.
  Ast.AstIndex0{} -> Ast.AstPrimalPart t
  Ast.AstSum0{} -> Ast.AstPrimalPart t
  Ast.AstDot0{} -> Ast.AstPrimalPart t
  Ast.AstDot1InS{} -> Ast.AstPrimalPart t
  Ast.AstMatmul2S{} -> Ast.AstPrimalPart t

  Ast.AstBoolNotK{} -> Ast.AstPrimalPart t
  Ast.AstBoolNotS{} -> Ast.AstPrimalPart t
  Ast.AstBoolAndK{} -> Ast.AstPrimalPart t
  Ast.AstBoolAndS{} -> Ast.AstPrimalPart t
  Ast.AstLeqK{} -> Ast.AstPrimalPart t
  Ast.AstLeq{} -> Ast.AstPrimalPart t
  Ast.AstLeqS{} -> Ast.AstPrimalPart t

-- Note how this can't be pushed down into, say, multiplication, because it
-- multiplies the dual part by the primal part. Addition is fine, though.
astDualPart :: AstTensor AstMethodLet FullSpan y
            -> AstTensor AstMethodLet DualSpan y
astDualPart t = case t of
  Ast.AstPair t1 t2 -> astPair (astDualPart t1) (astDualPart t2)
  Ast.AstProject1{} -> Ast.AstDualPart t
  Ast.AstProject2{} -> Ast.AstDualPart t
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map astDualPart l)
  Ast.AstSum snat stk v ->
    astSum snat stk (astDualPart v)
  Ast.AstReplicate snat stk v ->
    astReplicate snat stk (astDualPart v)
  Ast.AstMapAccumLDer k bftk eftk (AstLambda varf vf)
                                  (AstLambda vard vd)
                                  (AstLambda varr vr) acc0 es ->
    let varf2 = respanVarName varf
        astf2 = fromDual $ astVar varf2
        vf2 = astDualPart $ substituteAst astf2 varf vf
        vard2 = respanVarName vard
        astd2 = fromDual $ astVar vard2
        vd2 = astDualPart $ substituteAst astd2 vard vd
        varr2 = respanVarName varr
        astr2 = fromDual $ astVar varr2
        vr2 = astDualPart $ substituteAst astr2 varr vr
    in astMapAccumLDer k bftk eftk (AstLambda varf2 vf2)
                                   (AstLambda vard2 vd2)
                                   (AstLambda varr2 vr2)
                       (astDualPart acc0) (astDualPart es)
  Ast.AstApply{} -> Ast.AstDualPart t
  Ast.AstVar{} -> Ast.AstDualPart t
  Ast.AstCond b a2 a3 -> astCond b (astDualPart a2) (astDualPart a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = astDualPart v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var u (astDualPart v)

  Ast.AstFromPrimal v ->
    let ftk = ftkAst v
    in Ast.AstDualPart $ fromPlain
       $ astConcrete ftk (tdefTarget ftk)
           -- let's hope this is smaller than v
  Ast.AstFromDual v -> v
  Ast.AstFromPlain v ->  -- TODO: are deltas zeroed enough here?
    let ftk = ftkAst v
    in Ast.AstDualPart $ fromPlain
       $ astConcrete ftk (tdefTarget ftk)
           -- let's hope this is smaller than v

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
    astIndexS shn (astDualPart v) ix
  Ast.AstScatterS shm shn shp v (vars, ix) ->
    astScatterS shm shn shp (astDualPart v) (vars, ix)
  Ast.AstGatherS shm shn shp v (vars, ix) ->
    astGatherS shm shn shp (astDualPart v) (vars, ix)
  Ast.AstAppendS x y -> astAppendS (astDualPart x) (astDualPart y)
  Ast.AstSliceS i n k v -> astSliceS i n k (astDualPart v)
  Ast.AstReverseS v -> astReverseS (astDualPart v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astDualPart v)
  Ast.AstReshapeS sh v -> astReshapeS sh (astDualPart v)

  -- Most conversions need to stay down here to cancel out.
  Ast.AstConvert c a ->
    if checkAstConvUp c a
    then astConvert c $ astDualPart a
    else Ast.AstDualPart t

  -- These should not appear in this context unless via wacky tests.
  Ast.AstIndex0{} -> Ast.AstDualPart t
  Ast.AstSum0{} -> Ast.AstDualPart t
  Ast.AstDot0{} -> Ast.AstDualPart t
  Ast.AstDot1InS{} -> Ast.AstDualPart t
  Ast.AstMatmul2S{} -> Ast.AstDualPart t

  _ -> Ast.AstDualPart t

astPlainPart :: forall y s. KnownSpan s
             => AstTensor AstMethodLet s y
             -> AstTensor AstMethodLet PlainSpan y
astPlainPart t = case t of
  _ | SPlainSpan <- knownSpan @s -> t
  Ast.AstPair t1 t2 -> astPair (astPlainPart t1) (astPlainPart t2)
  -- We really need equality saturation...
  Ast.AstProject1 u@Ast.AstMapAccumLDer{} -> astProject1 $ astPlainPart u
  Ast.AstProject2 u@Ast.AstMapAccumLDer{} -> astProject2 $ astPlainPart u
  Ast.AstProject1 u@(Ast.AstProject1 Ast.AstMapAccumLDer{}) ->
    astProject1 $ astPlainPart u
  Ast.AstProject1 u@(Ast.AstProject2 Ast.AstMapAccumLDer{}) ->
    astProject1 $ astPlainPart u
  Ast.AstProject2 u@(Ast.AstProject2 Ast.AstMapAccumLDer{}) ->
    astProject2 $ astPlainPart u
  Ast.AstProject2 u@(Ast.AstProject1 Ast.AstMapAccumLDer{}) ->
    astProject2 $ astPlainPart u
  Ast.AstProject1{} -> Ast.AstPlainPart t
  Ast.AstProject2{} -> Ast.AstPlainPart t
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map astPlainPart l)
  Ast.AstSum snat stk v ->
    astSum snat stk (astPlainPart v)
  Ast.AstReplicate snat stk v ->
    astReplicate snat stk (astPlainPart v)
  Ast.AstMapAccumLDer k bftk eftk (AstLambda varf vf)
                                  (AstLambda vard vd)
                                  (AstLambda varr vr) acc0 es ->
    let varf2 = respanVarName varf
        astf2 = fromPlain $ astVar varf2
        vf2 = astPlainPart $ substituteAst astf2 varf vf
        vard2 = respanVarName vard
        astd2 = fromPlain $ astVar vard2
        vd2 = astPlainPart $ substituteAst astd2 vard vd
        varr2 = respanVarName varr
        astr2 = fromPlain $ astVar varr2
        vr2 = astPlainPart $ substituteAst astr2 varr vr
    in astMapAccumLDer k bftk eftk (AstLambda varf2 vf2)
                                   (AstLambda vard2 vd2)
                                   (AstLambda varr2 vr2)
                       (astPlainPart acc0) (astPlainPart es)
  Ast.AstApply{} -> Ast.AstPlainPart t
  Ast.AstVar{} -> Ast.AstPlainPart t  -- the only normal form
  Ast.AstCond b a2 a3 -> astCond b (astPlainPart a2) (astPlainPart a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = astPlainPart v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var u (astPlainPart v)

  Ast.AstPrimalPart v -> astPlainPart v
  Ast.AstDualPart{} -> Ast.AstPlainPart t
  Ast.AstFromPrimal v -> astPlainPart v
  Ast.AstFromDual v ->
    let ftk = ftkAst v
    in astConcrete ftk (tdefTarget ftk)
  Ast.AstFromPlain v -> v

  AstPlusK u v -> astPlainPart u + astPlainPart v
  AstTimesK u v -> astPlainPart u * astPlainPart v
  Ast.AstN1K NegateOp u -> negate (astPlainPart u)
  Ast.AstN1K AbsOp u -> abs (astPlainPart u)
  Ast.AstN1K SignumOp u -> signum (astPlainPart u)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (astPlainPart u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (astPlainPart u) (astPlainPart v)
  Ast.AstI2K QuotOp u v -> quotH (astPlainPart u) (astPlainPart v)
  Ast.AstI2K RemOp u v -> remH (astPlainPart u) (astPlainPart v)
  Ast.AstCastK v -> astCastK $ astPlainPart v

  AstPlusS u v -> astPlainPart u + astPlainPart v
  AstTimesS u v -> astPlainPart u * astPlainPart v
  Ast.AstN1S NegateOp u -> negate (astPlainPart u)
  Ast.AstN1S AbsOp u -> abs (astPlainPart u)
  Ast.AstN1S SignumOp u -> signum (astPlainPart u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astPlainPart u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (astPlainPart u) (astPlainPart v)
  Ast.AstI2S QuotOp u v -> quotH (astPlainPart u) (astPlainPart v)
  Ast.AstI2S RemOp u v -> remH (astPlainPart u) (astPlainPart v)
  Ast.AstCastS v -> astCastS $ astPlainPart v

  Ast.AstIndexS shn v ix ->
    astIndexS shn (astPlainPart v) ix
  Ast.AstScatterS shm shn shp v (vars, ix) ->
    astScatterS shm shn shp (astPlainPart v) (vars, ix)
  Ast.AstGatherS shm shn shp v (vars, ix) ->
    astGatherS shm shn shp (astPlainPart v) (vars, ix)
  Ast.AstAppendS x y -> astAppendS (astPlainPart x) (astPlainPart y)
  Ast.AstSliceS i n k v -> astSliceS i n k (astPlainPart v)
  Ast.AstReverseS v -> astReverseS (astPlainPart v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astPlainPart v)
  Ast.AstReshapeS sh v -> astReshapeS sh (astPlainPart v)

  -- Most conversions need to stay down here to cancel out.
  Ast.AstConvert c a ->
    if checkAstConvUp c a
    then astConvert c $ astPlainPart a
    else Ast.AstPlainPart t

  -- These should not appear in this context unless via wacky tests.
  Ast.AstIndex0{} -> Ast.AstPlainPart t
  Ast.AstSum0{} -> Ast.AstPlainPart t
  Ast.AstDot0{} -> Ast.AstPlainPart t
  Ast.AstDot1InS{} -> Ast.AstPlainPart t
  Ast.AstMatmul2S{} -> Ast.AstPlainPart t

astConcreteK :: GoodScalar r
             => Concrete (TKScalar r)
             -> AstTensor AstMethodLet PlainSpan (TKScalar r)
astConcreteK = AstConcreteK . unConcrete

astFloorK :: (GoodScalar r1, Differentiable r1, NumScalar r2, Integral r2)
          => AstTensor AstMethodLet PlainSpan (TKScalar r1)
          -> AstTensor AstMethodLet PlainSpan (TKScalar r2)
astFloorK t = case t of
  Ast.AstLet var u v -> astLet var u (astFloorK v)
  -- This increases work and term size, because conditional is eager.
  -- Ast.AstCond b a2 a3 -> Ast.AstCond b (astFloorK a2) (astFloorK a3)
  -- These values are small, so we can simplify them ASAP.
  AstConcreteK k -> astConcreteK (tkfloor $ Concrete k)
  Ast.AstFloorK v -> astFloorK v
  Ast.AstFromIntegralK v -> astFromIntegralK v
  Ast.AstCastK v -> astFloorK v
  _ -> Ast.AstFloorK t

-- Beware that increasing the number of calls to this constructor
-- sometimes increases runtime, because not enough copies cancel out.
-- Hence the commented out rules below.
astFromIntegralK :: forall r1 r2. (NumScalar r1, Integral r1, NumScalar r2)
                 => AstTensor AstMethodLet PlainSpan (TKScalar r1)
                 -> AstTensor AstMethodLet PlainSpan (TKScalar r2)
astFromIntegralK t = case t of
  _ | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) -> t
  Ast.AstLet var u v -> astLet var u (astFromIntegralK v)
  AstConcreteK k -> astConcreteK (tkfromIntegral $ Concrete k)
  Ast.AstN1K NegateOp u -> negate (astFromIntegralK u)
  Ast.AstN1K AbsOp u -> abs (astFromIntegralK u)
  Ast.AstN1K SignumOp u -> signum (astFromIntegralK u)
  Ast.AstFromIntegralK v -> astFromIntegralK v
  _ -> Ast.AstFromIntegralK t

astCastK :: forall r1 r2 s.
            ( NumScalar r1, Differentiable r1, NumScalar r2, Differentiable r2
            , KnownSpan s )
         => AstTensor AstMethodLet s (TKScalar r1)
         -> AstTensor AstMethodLet s (TKScalar r2)
astCastK t = case t of
  _ | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) -> t
  Ast.AstLet var u v -> astLet var u (astCastK v)
  AstConcreteK k -> astConcreteK (tkcast $ Concrete k)
  -- TODO: which should go deeper, casts or fromPrimal? Or maybe alternate
  -- in different phases to make sure both can cancel out?
  -- Rethink. For now, astFromPrimal is not called, to avoid loops.
  -- The same with many others.
  Ast.AstFromPrimal v -> fromPrimal $ astCastK v
  Ast.AstFromDual v -> fromDual $ astCastK v
  Ast.AstFromPlain v -> fromPlain $ astCastK v
  Ast.AstN1K NegateOp u -> negate (astCastK u)
  Ast.AstN1K AbsOp u -> abs (astCastK u)
  Ast.AstN1K SignumOp u -> signum (astCastK u)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (astCastK u)
  Ast.AstFromIntegralK v -> astFromIntegralK v
  Ast.AstCastK v -> astCastK v
  _ -> Ast.AstCastK t

astArgMinK :: NumScalar r
           => AstTensor AstMethodLet PlainSpan (TKS '[n] r)
           -> AstTensor AstMethodLet PlainSpan (TKScalar Int)
astArgMinK t = case t of
  Ast.AstReplicate{} -> 0  -- we mask undefined if n is zero; tough luck
  Ast.AstLet var u v -> astLet var u (astArgMinK v)
  AstConcreteS v -> astConcreteK (tkargMin $ Concrete v)
  Ast.AstN1S NegateOp u -> astArgMaxK u
  Ast.AstFromIntegralS v -> astArgMinK v
  Ast.AstCastS v -> astArgMinK v
  Ast.AstIotaS{} -> 0
  _ -> Ast.AstArgMinK t

astArgMaxK :: NumScalar r
           => AstTensor AstMethodLet PlainSpan (TKS '[n] r)
           -> AstTensor AstMethodLet PlainSpan (TKScalar Int)
astArgMaxK t = case t of
  Ast.AstReplicate{} -> 0
  Ast.AstLet var u v -> astLet var u (astArgMaxK v)
  AstConcreteS v -> astConcreteK (tkargMax $ Concrete v)
  Ast.AstN1S NegateOp u -> astArgMinK u
  Ast.AstFromIntegralS v -> astArgMaxK v
  Ast.AstCastS v -> astArgMaxK v
  Ast.AstIotaS{} -> 0
  _ -> Ast.AstArgMaxK t

astConcreteS :: GoodScalar r
             => Concrete (TKS sh r)
             -> AstTensor AstMethodLet PlainSpan (TKS sh r)
astConcreteS = AstConcreteS . unConcrete

astFloorS :: forall r1 r2 sh.
             (GoodScalar r1, Differentiable r1, NumScalar r2, Integral r2)
          => AstTensor AstMethodLet PlainSpan (TKS sh r1)
          -> AstTensor AstMethodLet PlainSpan (TKS sh r2)
astFloorS t = case t of
  _ | FTKS (snat :$$ sh2) _ <- ftkAst t
    , Just u <- unRepl1 t ->
      astReplicate snat (STKS sh2 STKScalar) (astFloorS u)
  Ast.AstBuild1 snat (STKS sh2 STKScalar) (var, v) ->
    let !v2 = astFloorS v
    in Ast.AstBuild1 snat (STKS sh2 STKScalar) (var, v2)
  Ast.AstBuild1 snat STKScalar (var, v) ->
    let !v2 = astFloorK v
    in Ast.AstBuild1 snat STKScalar (var, v2)
  Ast.AstLet var u v -> astLet var u (astFloorS v)
  Ast.AstFloorS v -> astFloorS v
  Ast.AstFromIntegralS v -> astFromIntegralS v
  Ast.AstCastS v -> astFloorS v
  Ast.AstScatterS shm shn shp v (vars, ix) ->
    astScatterS shm shn shp (astFloorS v) (vars, ix)
  Ast.AstGatherS shm shn shp v (vars, ix) ->
    astGatherS shm shn shp (astFloorS v) (vars, ix)
  Ast.AstIotaS snat -> Ast.AstIotaS snat
  Ast.AstReverseS v -> astReverseS (astFloorS v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astFloorS v)
  Ast.AstReshapeS sh v -> astReshapeS sh (astFloorS v)
  AstConvUpSFromK a -> astConvUpSFromK (astFloorK a)
  _ -> Ast.AstFloorS t

astFromIntegralS :: forall r1 r2 sh. (NumScalar r1, NumScalar r2, Integral r1)
                 => AstTensor AstMethodLet PlainSpan (TKS sh r1)
                 -> AstTensor AstMethodLet PlainSpan (TKS sh r2)
astFromIntegralS t = case t of
  _ | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) -> t
  _ | FTKS (snat :$$ sh2) _ <- ftkAst t
    , Just u <- unRepl1 t ->
      astReplicate snat (STKS sh2 STKScalar) (astFromIntegralS u)
--  Ast.AstFromVector snat (STKS sh STKScalar) l ->
--   astFromVector snat (STKS sh STKScalar) (V.map astFromIntegralS l)
--  Ast.AstFromVector snat STKScalar l ->
--   astFromVector snat STKScalar (V.map astFromIntegralK l)
  Ast.AstBuild1 snat (STKS sh2 STKScalar) (var, v) ->
    let !v2 = astFromIntegralS v
    in Ast.AstBuild1 snat (STKS sh2 STKScalar) (var, v2)
  Ast.AstBuild1 snat STKScalar (var, v) ->
    let !v2 = astFromIntegralK v
    in Ast.AstBuild1 snat STKScalar (var, v2)
  Ast.AstLet var u v -> astLet var u (astFromIntegralS v)
  Ast.AstN1S NegateOp u -> negate (astFromIntegralS u)
  Ast.AstN1S AbsOp u -> abs (astFromIntegralS u)
  Ast.AstN1S SignumOp u -> signum (astFromIntegralS u)
  Ast.AstFromIntegralS v -> astFromIntegralS v
--  Ast.AstIndexS shn v ix -> astIndexS shn (astFromIntegralS v) ix
    -- increases work; also index goes into fromIntegral, so we'd loop
  Ast.AstScatterS shm shn shp v (vars, ix) ->
    astScatterS shm shn shp (astFromIntegralS v) (vars, ix)
  Ast.AstGatherS shm shn shp v (vars, ix) ->
    astGatherS shm shn shp (astFromIntegralS v) (vars, ix)
  Ast.AstIotaS snat -> Ast.AstIotaS snat
--  Ast.AstSliceS i n k v -> astSliceS i n k (astFromIntegralS v)
  Ast.AstReverseS v -> astReverseS (astFromIntegralS v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astFromIntegralS v)
  Ast.AstReshapeS sh v -> astReshapeS sh (astFromIntegralS v)
  AstConvUpSFromK a -> astConvUpSFromK (astFromIntegralK a)
  _ -> Ast.AstFromIntegralS t

astCastS :: forall r1 r2 s sh.
            ( NumScalar r1, Differentiable r1
            , NumScalar r2, Differentiable r2, KnownSpan s )
         => AstTensor AstMethodLet s (TKS sh r1)
         -> AstTensor AstMethodLet s (TKS sh r2)
astCastS t = case t of
  _ | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) -> t
  _ | FTKS (snat :$$ sh2) _ <- ftkAst t
    , Just u <- unRepl1 t ->
      astReplicate snat (STKS sh2 STKScalar) (astCastS u)
--  Ast.AstFromVector snat (STKS sh STKScalar) l ->
--   astFromVector snat (STKS sh STKScalar) (V.map astCastS l)
--  Ast.AstFromVector snat STKScalar l ->
--   astFromVector snat STKScalar (V.map astCastK l)
  {- This (and other similar rules) is bad, because it changes semantics
     and also impacts performance negatively (a is larger than sum a):
  Ast.AstSum snat (STKS sh STKScalar) a ->
    astSum snat (STKS sh STKScalar) (astCastS a) -}
  Ast.AstBuild1 snat (STKS sh2 STKScalar) (var, v) ->
    let !v2 = astCastS v
    in Ast.AstBuild1 snat (STKS sh2 STKScalar) (var, v2)
  Ast.AstBuild1 snat STKScalar (var, v) ->
    let !v2 = astCastK v
    in Ast.AstBuild1 snat STKScalar (var, v2)
  Ast.AstLet var u v -> astLet var u (astCastS v)
  -- These (rarely) loop if ast* is used instead of Ast.Ast*.
  Ast.AstPrimalPart a -> Ast.AstPrimalPart $ astCastS a
  Ast.AstDualPart a -> Ast.AstDualPart $ astCastS a
  Ast.AstPlainPart a -> Ast.AstPlainPart $ astCastS a
  Ast.AstFromPrimal v -> fromPrimal $ astCastS v
  Ast.AstFromDual v -> fromDual $ astCastS v
  Ast.AstFromPlain v -> fromPlain $ astCastS v
  Ast.AstN1S NegateOp u -> negate (astCastS u)
  Ast.AstN1S AbsOp u -> abs (astCastS u)
  Ast.AstN1S SignumOp u -> signum (astCastS u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astCastS u)
  Ast.AstFromIntegralS v -> astFromIntegralS v
  Ast.AstCastS v -> astCastS v
--  Ast.AstIndexS shn v ix -> astIndexS shn (astCastS v) ix
    -- increases work; also index goes into fromIntegral, so we'd loop
  Ast.AstScatterS shm shn shp v (vars, ix) ->
    astScatterS shm shn shp (astCastS v) (vars, ix)
  Ast.AstGatherS shm shn shp v (vars, ix) ->
    astGatherS shm shn shp (astCastS v) (vars, ix)
  Ast.AstIotaS snat -> Ast.AstIotaS snat
--  Ast.AstSliceS i n k v -> astSliceS i n k (astCastS v)
  Ast.AstReverseS v -> astReverseS (astCastS v)
  Ast.AstTransposeS perm v -> astTransposeS perm (astCastS v)
  Ast.AstReshapeS sh v -> astReshapeS sh (astCastS v)
  AstConvUpSFromK a -> astConvUpSFromK (astCastK a)
  _ -> Ast.AstCastS t

astIndexS
  :: forall shm shn s x. KnownSpan s
  => ShS shn
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) x) -> AstIxS AstMethodLet shm
  -> AstTensor AstMethodLet s (TKS2 shn x)
astIndexS = astIndexKnobsS defaultKnobs

astIndexKnobsS
  :: forall shm shn s r. KnownSpan s
  => SimplifyKnobs
  -> ShS shn
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
  -> AstIxS AstMethodLet shm
  -> AstTensor AstMethodLet s (TKS2 shn r)
astIndexKnobsS _ _ v0 ZIS = v0
astIndexKnobsS _ shn v0 (i1 :.$ _)
  | Just (lb, ub) <- intBounds i1
-- this doesn't work in GHC 9.10:
--      FTKS (snat :$$ _) x = ftkAst v0
  , FTKS (snat :$$ _) x <- ftkAst v0
  , ub < 0 || lb >= fromSNat' snat =
    let ftk = FTKS shn x
    in fromPlain $ astConcrete ftk (tdefTarget ftk)
astIndexKnobsS knobs shn v0 (Ast.AstCond b i1 i2 :.$ rest0)
  | knobPhase knobs `notElem` [PhaseUnspecified, PhaseVectorization] =
      -- don't undo vectorization tweaks
    astLetFun v0 $ \v ->
    shareIx rest0 $ \rest ->
    astCond b (astIndexKnobsS knobs shn v (i1 :.$ rest))
              (astIndexKnobsS knobs shn v (i2 :.$ rest))
astIndexKnobsS knobs shn v0 ix@(i1 :.$ rest1)
 | FTKS shmshn x <- ftkAst v0 =
 case Shaped.shsTakeIx @shn @shm Proxy shmshn ix of
  SNat @in1 :$$ (_ :: ShS shm1) ->
   let astIndex
         :: forall shm' shn' s' r'. KnownSpan s'
         => ShS shn'
         -> AstTensor AstMethodLet s' (TKS2 (shm' ++ shn') r')
         -> AstIxS AstMethodLet shm'
         -> AstTensor AstMethodLet s' (TKS2 shn' r')
       astIndex shn' v2 ix2 = astIndexKnobsS (deVect knobs) shn' v2 ix2
       astGather
         :: forall shm' shn' shp'.
            ShS shm' -> ShS shn' -> ShS shp'
         -> AstTensor AstMethodLet s (TKS2 (shp' ++ shn') r)
         -> (AstVarListS shm', AstIxS AstMethodLet shp')
         -> AstTensor AstMethodLet s (TKS2 (shm' ++ shn') r)
       astGather shm' shn' shp' v2 (vars2, ix2) =
         astGatherKnobsS (deVect knobs) shm' shn' shp' v2 (vars2, ix2)
   in case v0 of
   Ast.AstProject1{} -> Ast.AstIndexS shn v0 ix
   Ast.AstProject2{} -> Ast.AstIndexS shn v0 ix
   Ast.AstFromVector _ STKS{} l | AstConcreteK i <- i1 ->
     astIndex shn (l V.! i) rest1
   Ast.AstFromVector _ STKScalar l | AstConcreteK i <- i1, ZIS <- rest1 ->
     astConvUpSFromK (l V.! i)
   Ast.AstFromVector{} | ZIS <- rest1 ->  -- normal form
     Ast.AstIndexS shn v0 ix
   Ast.AstFromVector snat STKS{} l ->
     shareIx rest1 $ \ !rest2 ->
       Ast.AstIndexS @'[in1] @shn shn (astFromVector snat (STKS shn (ftkToSTK x))
                                       $ V.map (\a -> astIndex shn a rest2) l)
                     (i1 :.$ ZIS)
   Ast.AstSum snat@(SNat @k1) STKS{} v ->
     let perm3 = backpermCycle $ ixsLength ix + 1
     in Permutation.permFromListCont perm3 $ \(perm
                                               :: Permutation.Perm perm3P) ->
          gcastWith (unsafeCoerceRefl
                     :: Compare (Rank perm3P) (Rank (k1 : shm ++ shn))
                        :~: LT) $
          gcastWith (unsafeCoerceRefl
                     :: Permutation.PermutePrefix perm3P (k1 : (shm ++ shn))
                        :~: shm ++ (k1 : shn)) $
          fromMaybe (error "astIndexKnobsS: impossible non-permutation")
          $ Permutation.permCheckPermutation perm
          $ astSum snat (STKS shn (ftkToSTK x))
          $ astIndex @shm @(k1 : shn) (snat :$$ shn)
                     (astTransposeS @perm3P @(k1 : shm ++ shn) perm v)
                     ix
   Ast.AstReplicate _ STKS{} v ->
     let ftk = FTKS shn x
         defArr = fromPlain $ astConcrete ftk (tdefTarget ftk)
     in case 0 <=. i1 &&* i1 <=. valueOf @in1 - 1 of
       AstConcreteK b -> if b then astIndex shn v rest1 else defArr
       _ -> Ast.AstIndexS shn v0 ix
   Ast.AstReplicate _ STKScalar v | ZIS <- rest1 ->
     let ftk = FTKS shn x
         defArr = fromPlain $ astConcrete ftk (tdefTarget ftk)
     in case 0 <=. i1 &&* i1 <=. valueOf @in1 - 1 of
       AstConcreteK b -> if b then astConvUpSFromK v else defArr
       _ -> Ast.AstIndexS shn v0 ix
   Ast.AstApply{} -> Ast.AstIndexS shn v0 ix
   Ast.AstVar{} -> Ast.AstIndexS shn v0 ix
   Ast.AstCond b v w ->
     shareIx ix $ \ !ix2 ->
       astCond b (astIndexKnobsS knobs shn v ix2)
                 (astIndexKnobsS knobs shn w ix2)
   {- This is wrong: in a counterfactual case, astLet assigns OOB i to var2,
      violating the invariant about variables bounds:
   Ast.AstBuild1 (SNat @k) STKS{} (var2, v) ->
     let ftk = FTKS shn x
         defArr = fromPlain $ astConcrete ftk (tdefTarget ftk)
     in astLetFun i1 $ \i ->
     astCond (0 <=. i &&* i <=. valueOf @k - 1)
             (astIndex shn (astLet var2 i v) rest1)
             defArr -}
   Ast.AstBuild1 (SNat @k) STKS{} (var2, v) ->
     let ftk = FTKS shn x
         defArr = fromPlain $ astConcrete ftk (tdefTarget ftk)
     in case 0 <=. i1 &&* i1 <=. valueOf @k - 1 of
       AstConcreteK b ->
         if b then astIndex shn (astLet var2 i1 v) rest1 else defArr
       _ -> Ast.AstIndexS shn v0 ix
   Ast.AstBuild1 (SNat @k) STKScalar (var2, v) | ZIS <- rest1 ->
     let ftk = FTKS shn x
         defArr = fromPlain $ astConcrete ftk (tdefTarget ftk)
     in case 0 <=. i1 &&* i1 <=. valueOf @k - 1 of
       AstConcreteK b ->
         if b then astConvUpSFromK $ astLet var2 i1 v else defArr
       _ -> Ast.AstIndexS shn v0 ix

   Ast.AstLet var u v -> astLet var u (astIndexKnobsS knobs shn v ix)

   Ast.AstPrimalPart{} -> Ast.AstIndexS shn v0 ix  -- must be a NF
   Ast.AstDualPart{} -> Ast.AstIndexS shn v0 ix
   Ast.AstPlainPart{} -> Ast.AstIndexS shn v0 ix
   Ast.AstFromPrimal v -> fromPrimal $ astIndexKnobsS knobs shn v ix
   Ast.AstFromDual v -> fromDual $ astIndexKnobsS knobs shn v ix
   Ast.AstFromPlain v -> fromPlain $ astIndexKnobsS knobs shn v ix

   AstPlusS u v ->
     shareIx ix $ \ !ix2 ->
     astIndexKnobsS knobs shn u ix2 + astIndexKnobsS knobs shn v ix2
   AstTimesS u v ->
     shareIx ix $ \ !ix2 ->
     astIndexKnobsS knobs shn u ix2 * astIndexKnobsS knobs shn v ix2
   Ast.AstN1S NegateOp u -> negate (astIndexKnobsS knobs shn u ix)
   Ast.AstN1S AbsOp u -> abs (astIndexKnobsS knobs shn u ix)
   Ast.AstN1S SignumOp u -> signum (astIndexKnobsS knobs shn u ix)
   Ast.AstR1S opCode u -> Ast.AstR1S opCode (astIndexKnobsS knobs shn u ix)
   Ast.AstR2S opCode u v ->
     shareIx ix
     $ \ !ix2 -> Ast.AstR2S opCode (astIndexKnobsS knobs shn u ix2)
                                   (astIndexKnobsS knobs shn v ix2)
   Ast.AstI2S opCode u v ->
     shareIx ix
     $ \ !ix2 -> Ast.AstI2S opCode (astIndexKnobsS knobs shn u ix2)
                                   (astIndexKnobsS knobs shn v ix2)
   AstConcreteS a | AstConcreteK i <- i1 ->
     let u = withKnownShS (shsTail shmshn) $
             tsindex (Concrete a) (Concrete i :.$ ZIS)
     in astIndex shn (astConcreteS u) rest1
   AstConcreteS{} -> case unRepl1 v0 of
     Just u ->
       let ftk = FTKS shn x
           defArr = fromPlain $ astConcrete ftk (tdefTarget ftk)
       in case 0 <=. i1 &&* i1 <=. valueOf @in1 - 1 of
         AstConcreteK b -> if b then astIndex shn u rest1 else defArr
         _ -> Ast.AstIndexS shn v0 ix
     _ -> Ast.AstIndexS shn v0 ix
   Ast.AstFloorS v -> astFloorS $ astIndexKnobsS knobs shn v ix
   Ast.AstFromIntegralS v -> astFromIntegralS $ astIndexKnobsS knobs shn v ix
   Ast.AstCastS t -> astCastS $ astIndexKnobsS knobs shn t ix
   Ast.AstArgMinS @n1 @shz v -> case ftkAst v of
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
          Ast.AstArgMinS @(Head (shn ++ '[nl]))
                         @(Tail (shn ++ '[nl]))
          $ astIndexKnobsS @shm @(shn ++ '[nl]) knobs shnl v ix
   Ast.AstArgMaxS @n1 @shz v -> case ftkAst v of
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
          Ast.AstArgMaxS @(Head (shn ++ '[nl]))
                         @(Tail (shn ++ '[nl]))
          $ astIndexKnobsS @shm @(shn ++ '[nl]) knobs shnl v ix

   Ast.AstIndexS _ v (ix2 :: AstIxS AstMethodLet sh4)
     | Refl <- lemAppAssoc (Proxy @sh4) (Proxy @shm) (Proxy @shn) ->
       astIndexKnobsS knobs shn v (ix2 `ixsAppend` ix)
   Ast.AstScatterS shm7 shn7 shp7 v (vars, AstIntVar var5 :.$ ix2)
     | AstIntVar var6 <- i1, var6 == var5 ->
         astIndex shn (astScatterS shm7 shn7 (shsTail shp7)
                                   v (vars, ix2)) rest1
   Ast.AstScatterS shm7 shn7 shp7
                   v (vars, AstConcreteK i5 :.$ ix2)
     | AstConcreteK i6 <- i1 ->
         if i6 == i5
         then astIndex shn (astScatterS shm7 shn7 (shsTail shp7)
                                        v (vars, ix2)) rest1
         else let ftk = FTKS shn x
              in fromPlain $ astConcrete ftk (tdefTarget ftk)
   -- AstScatter sh v (vars2, ZIR) ->
   --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZIR)
   Ast.AstScatterS{} ->  -- normal form
     Ast.AstIndexS shn v0 ix
   -- This is not a possible normal form, but pattern needs to be exhaustive.
   Ast.AstGatherS @_ @_ @shp' _ _ _ v (ZS, ix2) ->
     gcastWith (unsafeCoerceRefl
               :: shp' ++ (in1 ': shm1) ++ shn
                  :~: shp' ++ (in1 ': shm1 ++ shn)) $
     astIndex @(shp' ++ shm) @shn shn v (ix2 `ixsAppend` ix)
   Ast.AstGatherS @_ @shn' shm'@(SNat @m71 :$$ (_ :: ShS shm71)) shn' shp'
                  v (var2 ::$ vars, ix2) ->
     gcastWith (unsafeCoerceRefl :: shm71 ++ shn' :~: shm1 ++ shn) $
     let ftk = FTKS shn x
         defArr = fromPlain $ astConcrete ftk (tdefTarget ftk)
         w :: AstTensor AstMethodLet s (TKS2 (shm1 ++ shn) r)
         w = astGather (shsTail shm') shn' shp' v (vars, ix2)
         u = astLet var2 i1 $ astIndex @shm1 @shn shn w rest1
           -- this let makes it impossible to use astCond when i1 is OOB
     in case 0 <=. i1 &&* i1 <=. valueOf @m71 - 1 of
       AstConcreteK b -> if b then u else defArr
       _ -> Ast.AstIndexS shn v0 ix
   Ast.AstIotaS (SNat @k) -> case testEquality shn ZSS of
     Just Refl ->
       let ftk = FTKS ZSS x
           defArr = fromPlain $ astConcrete ftk (tdefTarget ftk)
       in astLetFun i1 $ \i ->
         astCond (0 <=. i &&* i <=. valueOf @k - 1)
                 (astFromIntegralS $ astConvUpSFromK i)
                 defArr
     _ -> error "astIndexKnobsS: shape not []"
   Ast.AstAppendS u v | FTKS (SNat @m :$$ _) _ <- ftkAst u ->
     if knobPhase knobs == PhaseExpansion then
       astLetFun i1 $ \i ->
       shareIx rest1 $ \ !rest2 ->
       let ulen = valueOf @m
           ix1 = i :.$ rest2
           ix2 = i - ulen :.$ rest2
       in case ulen <=. i of
         AstConcreteK b -> if b then astIndex shn v ix2 else astIndex shn u ix1
         bExpr ->
           -- This results in a larger term, so we consider this late.
           astCond bExpr (astIndex shn v ix2) (astIndex shn u ix1)
     else
       -- We don't need to share i1 and rest1 here and, in fact, we can't
       -- because we'd loop via building AstLet around the resulting AstIndexS.
       let ulen = valueOf @m
           ix1 = i1 :.$ rest1
           ix2 = i1 - ulen :.$ rest1
       in case ulen <=. i1 of
         AstConcreteK b -> if b then astIndex shn v ix2 else astIndex shn u ix1
         _ -> Ast.AstIndexS shn v0 ix
   Ast.AstSliceS i@(SNat @i) (SNat @n) k@SNat v ->
     astLetFun i1 $ \iShared ->
     let ftk = FTKS shn x
         defArr = fromPlain $ astConcrete ftk (tdefTarget ftk)
         b = (if fromSNat' i == 0 then true else 0 <=. iShared )
             &&* (if fromSNat' k == 0 then true else iShared <=. valueOf @n - 1)
         ii = valueOf @i + iShared
     in astCond b (astIndex shn v (ii :.$ rest1)) defArr
   Ast.AstReverseS v ->
     let iRev = valueOf @in1 - 1 - i1
     in astIndex shn v (iRev :.$ rest1)
   Ast.AstTransposeS @_ @sh2 perm v
     | gcompare (ixsRank ix) (Permutation.permRank perm) /= GLT ->
       -- TODO: remake once there's an S version of permInverse:
       permInverse perm $ \(permR :: Permutation.Perm permR) _ ->
       let ix2 :: AstIxS AstMethodLet (Permutation.PermutePrefix permR shm)
           ix2 = ixsPermutePrefix permR ix
       in gcastWith (unsafeCoerceRefl
                     :: sh2 :~: Permutation.PermutePrefix permR shm ++ shn) $
          astIndex @(Permutation.PermutePrefix permR shm) shn v ix2
   Ast.AstTransposeS @perm perm v
     | knobPhase knobs `elem` [PhaseVectorization, PhaseExpansion] ->
       astIndex shn (astTransposeAsGatherS @perm (deVect knobs) perm v) ix
   Ast.AstTransposeS{} -> Ast.AstIndexS shn v0 ix
   -- This results in a larger term, so we consider this late.
   Ast.AstReshapeS sh v | knobPhase knobs == PhaseExpansion
                          || shsLength sh <= 1 ->
     astIndex shn (astReshapeAsGatherS (deVect knobs) sh v) ix
   Ast.AstReshapeS{} -> Ast.AstIndexS shn v0 ix

   AstConvUp ftkz v -> case matchingFTK (ftkAst v) ftkz of
     Just Refl -> astIndexKnobsS knobs shn v ix
       -- rare, usually simplifies away earlier
     Nothing -> error "astIndexKnobsS: wrong tensor kinds in AstConvUp"
   -- These conversions need to stay down, so this is NF, see vectorization.
   Ast.AstConvert{} -> Ast.AstIndexS shn v0 ix

   -- These should not appear here unless via wacky tests.
   Ast.AstDot1InS{} -> Ast.AstIndexS shn v0 ix
   Ast.AstMatmul2S{} -> Ast.AstIndexS shn v0 ix

   Ast.AstBoolNotS{} -> Ast.AstIndexS shn v0 ix
   Ast.AstBoolAndS{} -> Ast.AstIndexS shn v0 ix
   Ast.AstLeqS{} -> Ast.AstIndexS shn v0 ix

-- TODO: compared to tletIx, it adds many lets, not one, but does not
-- create other (and non-simplified!) big terms and also uses astIsSmall,
-- so it's probably more efficient. Use this instead of tletIx
-- or design something even better.
--
-- See https://github.com/Mikolaj/horde-ad/issues/119.
shareIx :: forall s shm y. KnownSpan s
        => AstIxS AstMethodLet shm
        -> (AstIxS AstMethodLet shm -> AstTensor AstMethodLet s y)
        -> AstTensor AstMethodLet s y
{-# NOINLINE shareIx #-}
shareIx ix f = unsafePerformIO $ do
  let shareI :: AstInt AstMethodLet
             -> IO ( Maybe (IntVarName, AstInt AstMethodLet)
                   , AstInt AstMethodLet )
      shareI i | astIsSmall True i = return (Nothing, i)
      shareI i =
        -- i can be OOB, so we can't use shape to determine its bounds
        funToAstIntMaybeIO (intBounds i) $ \ (!varFresh, !astVarFresh) ->
          (Just (varFresh, i), astVarFresh)
  (bindings, ix2) <- mapAndUnzipM shareI (Foldable.toList ix)
  return $! foldl' (\v (var, u) -> astLet var u v)
                   (f $ ixsFromIxS ix ix2)
                   (catMaybes bindings)

-- TODO: fuse scatters, scatter and sum, and perhaps more (fromList?)
astScatterS :: forall shm shn shp r s. (KnownSpan s, TKAllNum r)
            => ShS shm -> ShS shn -> ShS shp
            -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
            -> (AstVarListS shm, AstIxS AstMethodLet shp)
            -> AstTensor AstMethodLet s (TKS2 (shp ++ shn) r)
astScatterS _ _ _ v (ZS, ZIS) = v
astScatterS _ shn shp@(k :$$ _) v0 (_,  i1 :.$ _)
  | Just (lb, ub) <- intBounds i1
  , let FTKS _ x = ftkAst v0
  , ub < 0 || lb >= fromSNat' k =
    let ftk = FTKS (shp `shsAppend` shn) x
    in fromPlain $ astConcrete ftk (tdefTarget ftk)
astScatterS shm shn shp@(SNat' @1 :$$ _) v (vars, AstConcreteK _ :.$ rest) =
    astReplicate (SNat @1) (STKS (shsTail shp
                                  `shsAppend` shn) (stkAstX v))
    $ astScatterS shm shn (shsTail shp) v (vars, rest)
astScatterS (SNat :$$ shm2) shn shp v (var ::$ vars, ix)
  | not $ var `varNameInIxS` ix =
      astScatterS shm2 shn shp
        (astSum SNat (STKS (shm2 `shsAppend` shn) (stkAstX v)) v)
        (vars, ix)
-- TODO? astScatterS v (ZR, ix) = update (rzero sh 0) ix v
astScatterS shm shn shp (Ast.AstLet var u v) (vars, ix) =
  astLet var u (astScatterS shm shn shp v (vars, ix))
astScatterS shm shn shp (Ast.AstFromPrimal v) (vars, ix) =
  fromPrimal $ astScatterS shm shn shp v (vars, ix)
astScatterS shm shn shp (Ast.AstFromDual v) (vars, ix) =
  fromDual $ astScatterS shm shn shp v (vars, ix)
astScatterS shm shn shp (Ast.AstFromPlain v) (vars, ix) =
  fromPlain $ astScatterS shm shn shp v (vars, ix)
astScatterS shm shn shp v (vars, ix) = Ast.AstScatterS shm shn shp v (vars, ix)

flipCompare :: forall (a :: Nat) b. Compare a b ~ GT
            => Proxy a -> Proxy b -> Compare b a :~: LT
flipCompare _ _ = unsafeCoerceRefl

astGatherS
  :: forall shm shn shp r s. KnownSpan s
  => ShS shm -> ShS shn -> ShS shp
  -> AstTensor AstMethodLet s (TKS2 (shp ++ shn) r)
  -> (AstVarListS shm, AstIxS AstMethodLet shp)
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
astGatherS = astGatherKnobsS defaultKnobs

-- Assumption: vars0 don't not occur in v0. The assumption only holds
-- when newly generated variables are fresh, which is the case as long
-- as resetVarCounter is not used. The assumption makes it easier to spot
-- bugs or corruption, hence we assert it in the code below.
astGatherKnobsS
  :: forall shm shn shp r s. KnownSpan s
  => SimplifyKnobs
  -> ShS shm -> ShS shn -> ShS shp
  -> AstTensor AstMethodLet s (TKS2 (shp ++ shn) r)
  -> (AstVarListS shm, AstIxS AstMethodLet shp)
  -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) r)
astGatherKnobsS _ _ _ _ v0 (!vars0, !_ix0)
  | Foldable.any (`varNameInAst` v0) vars0 =
    error $ "astGatherKnobsS: gather vars in v0: " ++ show (vars0, v0)
astGatherKnobsS knobs _ shn _ v0 (ZS, ix0) = astIndexKnobsS knobs shn v0 ix0
astGatherKnobsS _ shm _ _ v0 (_, ZIS) =
  astReplicateNS @shm @shn shm v0
astGatherKnobsS _ shm shn _shp v0 (_, i1 :.$ _)
  | Just (lb, ub) <- intBounds i1
-- this doesn't work in GHC 9.10:
--      FTKS (snat :$$ _) x = ftkAst v0
  , FTKS (snat :$$ _) x <- ftkAst v0
  , ub < 0 || lb >= fromSNat' snat =
    let ftk = FTKS (shm `shsAppend` shn) x
    in fromPlain $ astConcrete ftk (tdefTarget ftk)
astGatherKnobsS knobs shm@(k :$$ _) shn shp v0 (var1 ::$ vars1, ix0)
  | not (var1 `varNameInIxS` ix0) =
    astReplicate k (STKS (shsTail shm `shsAppend` shn) (stkAstX v0))
                 (astGatherKnobsS knobs (shsTail shm) shn shp v0 (vars1, ix0))
astGatherKnobsS knobs shm shn shp v0 (vars0@(_ ::$ _), ix0@(_ :.$ _))
  | let ixInit = ixsInit ix0
        varInit = listsInit vars0
        varLast = listsLast vars0
  , AstIntVar ixvarLast <- ixsLast ix0
  , ixvarLast == varLast
  , not (varLast `varNameInIxS` ixInit)
  , kLast@SNat <- shsLast shm
  , Just Refl <- testEquality kLast (shsLast shp) =
    gcastWith (unsafeCoerceRefl
               :: Init shp ++ (Last shm ': shn) :~: shp ++ shn) $
    gcastWith (unsafeCoerceRefl
               :: Init shm ++ (Last shm ': shn) :~: shm ++ shn) $
    astGatherKnobsS knobs (shsInit shm) (kLast :$$ shn) (shsInit shp)
                    v0 (varInit, ixInit)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstCond
           (Ast.AstBoolAndK a@(AstLeqInt (AstConcreteK j) AstIntVar{}) b)
           v w :.$ prest )
    | j <= 0 || j >= fromSNat' m || ixIsSmall prest =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, i :.$ prest)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstLet varN uN
           (Ast.AstCond
              (Ast.AstBoolAndK a@(AstLeqInt (AstConcreteK j) AstIntVar{}) b)
              v w) :.$ prest )
    | j <= 0 || j >= fromSNat' m || ixIsSmall prest && astIsSmall True uN =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, Ast.AstLet varN uN i :.$ prest)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstCond
           (Ast.AstBoolAndK a@(AstLeqInt (AstConcreteK j)
                                         (Ast.AstN1K NegateOp AstIntVar{})) b)
           v w :.$ prest )
    | - j + 1 <= 0 || - j + 1 >= fromSNat' m || ixIsSmall prest =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, i :.$ prest)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstLet varN uN
           (Ast.AstCond
              (Ast.AstBoolAndK
                 a@(AstLeqInt (AstConcreteK j)
                              (Ast.AstN1K NegateOp AstIntVar{})) b)
              v w) :.$ prest )
    | - j + 1 <= 0 || - j + 1 >= fromSNat' m
      || ixIsSmall prest && astIsSmall True uN =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, Ast.AstLet varN uN i :.$ prest)

astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstCond
           (Ast.AstBoolAndK
              a@(Ast.AstBoolNotK (AstLeqInt (AstConcreteK j) AstIntVar{})) b)
           v w :.$ prest )
    | j <= 0 || j >= fromSNat' m || ixIsSmall prest =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, i :.$ prest)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstLet varN uN
           (Ast.AstCond
              (Ast.AstBoolAndK
                 a@(Ast.AstBoolNotK (AstLeqInt (AstConcreteK j) AstIntVar{})) b)
              v w) :.$ prest )
    | j <= 0 || j >= fromSNat' m || ixIsSmall prest && astIsSmall True uN =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, Ast.AstLet varN uN i :.$ prest)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstCond
           (Ast.AstBoolAndK
              a@(Ast.AstBoolNotK (AstLeqInt (AstConcreteK j)
                                           (Ast.AstN1K NegateOp
                                                       AstIntVar{}))) b)
           v w :.$ prest )
    | - j + 1 <= 0 || - j + 1 >= fromSNat' m || ixIsSmall prest =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, i :.$ prest)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstLet varN uN
           (Ast.AstCond
              (Ast.AstBoolAndK
                 a@(Ast.AstBoolNotK (AstLeqInt (AstConcreteK j)
                                              (Ast.AstN1K NegateOp
                                                          AstIntVar{}))) b)
              v w) :.$ prest )
    | - j + 1 <= 0 || - j + 1 >= fromSNat' m
      || ixIsSmall prest && astIsSmall True uN =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, Ast.AstLet varN uN i :.$ prest)

astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstCond
      (Ast.AstBoolAndK
         a@(Ast.AstBoolNotK
              (Ast.AstBoolAndK (AstLeqInt (AstConcreteK j) AstIntVar{}) _)) b)
      v w :.$ prest )
    | j <= 0 || j >= fromSNat' m || ixIsSmall prest =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, i :.$ prest)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstLet varN uN
           (Ast.AstCond
              (Ast.AstBoolAndK
                 a@(Ast.AstBoolNotK
                      (Ast.AstBoolAndK (AstLeqInt (AstConcreteK j)
                                                  AstIntVar{}) _)) b)
              v w) :.$ prest )
    | j <= 0 || j >= fromSNat' m || ixIsSmall prest && astIsSmall True uN =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, Ast.AstLet varN uN i :.$ prest)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstCond
           (Ast.AstBoolAndK
              a@(Ast.AstBoolNotK
                   (Ast.AstBoolAndK (AstLeqInt (AstConcreteK j)
                                               (Ast.AstN1K NegateOp
                                                           AstIntVar{})) _)) b)
           v w :.$ prest )
    | - j + 1 <= 0 || - j + 1 >= fromSNat' m || ixIsSmall prest =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, i :.$ prest)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstLet varN uN
           (Ast.AstCond
              (Ast.AstBoolAndK
                 a@(Ast.AstBoolNotK
                      (Ast.AstBoolAndK
                         (AstLeqInt (AstConcreteK j)
                                    (Ast.AstN1K NegateOp
                                                AstIntVar{})) _)) b)
              v w) :.$ prest )
    | - j + 1 <= 0 || - j + 1 >= fromSNat' m
      || ixIsSmall prest && astIsSmall True uN =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, Ast.AstLet varN uN i :.$ prest)

astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstCond
           (Ast.AstBoolAndK
              a@(Ast.AstBoolNotK
                   (Ast.AstBoolAndK
                      (Ast.AstBoolNotK
                         (AstLeqInt (AstConcreteK j) AstIntVar{})) _)) b)
           v w :.$ prest )
    | j <= 0 || j >= fromSNat' m || ixIsSmall prest =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, i :.$ prest)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstLet varN uN
           (Ast.AstCond
              (Ast.AstBoolAndK
                 a@(Ast.AstBoolNotK
                      (Ast.AstBoolAndK
                         (Ast.AstBoolNotK (AstLeqInt (AstConcreteK j)
                                                    AstIntVar{})) _)) b)
              v w) :.$ prest )
    | j <= 0 || j >= fromSNat' m || ixIsSmall prest && astIsSmall True uN =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, Ast.AstLet varN uN i :.$ prest)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstCond
           (Ast.AstBoolAndK
              a@(Ast.AstBoolNotK
                   (Ast.AstBoolAndK
                      (Ast.AstBoolNotK
                         (AstLeqInt (AstConcreteK j)
                                   (Ast.AstN1K NegateOp AstIntVar{}))) _)) b)
           v w :.$ prest )
    | - j + 1 <= 0 || - j + 1 >= fromSNat' m || ixIsSmall prest =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, i :.$ prest)
astGatherKnobsS
  knobs shm@(m :$$ _) shn shp v0
  ( vars
  , Ast.AstLet varN uN
           (Ast.AstCond
              (Ast.AstBoolAndK
                 a@(Ast.AstBoolNotK
                      (Ast.AstBoolAndK
                         (Ast.AstBoolNotK
                            (AstLeqInt (AstConcreteK j)
                                       (Ast.AstN1K NegateOp
                                                   AstIntVar{}))) _)) b)
              v w) :.$ prest )
    | - j + 1 <= 0 || - j + 1 >= fromSNat' m
      || ixIsSmall prest && astIsSmall True uN =
  let i = astLetFun w $ \wShared -> astCond a (astCond b v wShared) wShared
  in astGatherKnobsS knobs shm shn shp v0 (vars, Ast.AstLet varN uN i :.$ prest)
-- Rules with AstConcreteK on the right hand side of AstPlusK are
-- not needed, thanks to the normal form of AstPlusK rewriting.
astGatherKnobsS knobs shm shn shp v0
  (vars, AstPlusK (AstConcreteK i) i1 :.$ prest)
  | Just (lb, ub) <- intBounds i1
  , lb >= 0  -- if not, we may need to apply astReverse first
  , FTKS (SNat @p :$$ _) x <- ftkAst v0 =
    if i >= 0 then
      withSNat i $ \(SNat @i) ->
      withSNat (min (valueOf @p - i) (ub + 1)) $ \(SNat @k) ->
        gcastWith (unsafeCoerceRefl :: (i + k <=? p) :~: True) $
        let v2 = astSliceS (SNat @i) (SNat @k) (SNat @(p - (i + k))) v0
        in astGatherKnobsS knobs shm shn (SNat @k :$$ shsTail shp)
                           v2 (vars, i1 :.$ prest)
             -- this gather may still index out of bounds, which is fine
    else
      withSNat (- i) $ \(SNat @i) ->
        let ftk = FTKS (SNat @i :$$ shsTail shp `shsAppend` shn) x
            v2 = fromPlain (astConcrete ftk (tdefTarget ftk))
                 `astAppendS`
                 v0
        in astGatherKnobsS knobs shm shn (SNat @(p + i) :$$ shsTail shp)
                           v2 (vars, i1 :.$ prest)
             -- this gather may still index out of bounds, which is fine
astGatherKnobsS knobs shm shn shp v0
  (vars, Ast.AstLet varN uN (AstPlusK (AstConcreteK i) i1) :.$ prest)
  | Just (lb, ub) <- intBounds i1
  , lb >= 0  -- if not, we may need to apply astReverse first
  , FTKS (SNat @p :$$ _) x <- ftkAst v0 =
    if i >= 0 then
      withSNat i $ \(SNat @i) ->
      withSNat (min (valueOf @p - i) (ub + 1)) $ \(SNat @k) ->
        gcastWith (unsafeCoerceRefl :: (i + k <=? p) :~: True) $
        let v2 = astSliceS (SNat @i) (SNat @k) (SNat @(p - (i + k))) v0
        in astGatherKnobsS knobs shm shn (SNat @k :$$ shsTail shp)
                           v2 (vars, Ast.AstLet varN uN i1 :.$ prest)
             -- this gather may still index out of bounds, which is fine
    else
      withSNat (- i) $ \(SNat @i) ->
        let ftk = FTKS (SNat @i :$$ shsTail shp `shsAppend` shn) x
            v2 = fromPlain (astConcrete ftk (tdefTarget ftk))
                 `astAppendS`
                 v0
        in astGatherKnobsS knobs shm shn (SNat @(p + i) :$$ shsTail shp)
                           v2 (vars, Ast.AstLet varN uN i1 :.$ prest)
             -- this gather may still index out of bounds, which is fine
astGatherKnobsS knobs shm@(SNat @m :$$ _) shn shp v0
  ( vars@(varm ::$ mrest)
  , Ast.AstCond (AstLeqInt (AstConcreteK j) (AstIntVar varp)) i1 i2
    :.$ prest )
  | varNameToAstVarId varm == varNameToAstVarId varp
  , j <= 0 || j >= valueOf @m || ixIsSmall prest =
    if | j <= 0 ->
         astGatherKnobsS knobs shm shn shp
                         v0 (vars, i1 :.$ prest)
       | j >= valueOf @m ->
         astGatherKnobsS knobs shm shn shp
                         v0 (vars, i2 :.$ prest)
       | otherwise ->
         withSNat j $ \(SNat @j) ->
         gcastWith (unsafeCoerceRefl :: (j <=? m) :~: True) $
         astLetFun v0 $ \v ->
         let varm2 = reboundsVarName (0, j - 1) varm
             varm3 = reboundsVarName (0, valueOf @m - j - 1) varm
         in astGatherKnobsS knobs (SNat @j :$$ shsTail shm) shn shp v
              ( (::$) @j (varm2) mrest
              , substituteAstIxS (astVar varm2)
                                 varm (i2 :.$ prest) )
            `astAppendS`
            astGatherKnobsS knobs (SNat @(m - j) :$$ shsTail shm) shn shp v
              ( (::$) @(m - j) (varm3) mrest
              , substituteAstIxS (AstConcreteK j + astVar varm3)
                                 varm (i1 :.$ prest) )
astGatherKnobsS knobs shm@(SNat @m :$$ _) shn shp v0
  ( vars@(varm ::$ mrest)
  , Ast.AstCond (AstLeqInt (AstConcreteK j)
                           (Ast.AstN1K NegateOp (AstIntVar varp))) i1 i2
    :.$ prest )
  | varNameToAstVarId varm == varNameToAstVarId varp
  , - j + 1 <= 0 || - j + 1 >= valueOf @m || ixIsSmall prest =
    if | - j + 1 <= 0 ->
         astGatherKnobsS knobs shm shn shp
                         v0 (vars, i2 :.$ prest)
       | - j + 1 >= valueOf @m ->
         astGatherKnobsS knobs shm shn shp
                         v0 (vars, i1 :.$ prest)
       | otherwise ->
         withSNat (- j + 1) $ \(SNat @mj) ->
         gcastWith (unsafeCoerceRefl :: (mj <=? m) :~: True) $
         astLetFun v0 $ \v ->
         let varm2 = reboundsVarName (0, valueOf @mj - 1) varm
             varm3 = reboundsVarName (0, valueOf @m - valueOf @mj - 1) varm
         in astGatherKnobsS knobs (SNat @mj :$$ shsTail shm) shn shp v
              ( (::$) @mj varm2 mrest
              , substituteAstIxS (astVar varm2)
-- TODO: when I use AstIntVar here, which is wrong, I get phantom errors;
-- make sure this vanished after the fixes in HEAD
                                 varm (i1 :.$ prest) )
            `astAppendS`
            astGatherKnobsS knobs (SNat @(m - mj) :$$ shsTail shm) shn shp v
              ( (::$) @(m - mj) varm3 mrest
              , substituteAstIxS (AstConcreteK (- j + 1) + astVar varm3)
                                 varm (i2 :.$ prest))
astGatherKnobsS knobs shm@(SNat @m :$$ _) shn shp v0
  ( vars@(varm ::$ mrest)
  , Ast.AstLet varN uN
      (Ast.AstCond (AstLeqInt (AstConcreteK j) (AstIntVar varp)) i1 i2)
      :.$ prest )
  | varNameToAstVarId varm == varNameToAstVarId varp
  , j <= 0 || j >= valueOf @m || ixIsSmall prest && astIsSmall True uN =
    if | j <= 0 ->
         astGatherKnobsS knobs shm shn shp
                         v0 (vars, Ast.AstLet varN uN i1 :.$ prest)
       | j >= valueOf @m ->
         astGatherKnobsS knobs shm shn shp
                         v0 (vars, Ast.AstLet varN uN i2 :.$ prest)
       | otherwise ->
         withSNat j $ \(SNat @j) ->
         gcastWith (unsafeCoerceRefl :: (j <=? m) :~: True) $
         astLetFun v0 $ \v ->
         let varm2 = reboundsVarName (0, j - 1) varm
             varm3 = reboundsVarName (0, valueOf @m - j - 1) varm
         in astGatherKnobsS knobs (SNat @j :$$ shsTail shm) shn shp v
              ( (::$) @j varm2 mrest
              , substituteAstIxS (astVar varm2) varm
                                 (Ast.AstLet varN uN i2 :.$ prest) )
            `astAppendS`
            astGatherKnobsS knobs (SNat @(m - j) :$$ shsTail shm) shn shp v
              ( (::$) @(m - j) varm3 mrest
              , substituteAstIxS (AstConcreteK j + astVar varm3)
                                 varm (Ast.AstLet varN uN i1 :.$ prest) )
astGatherKnobsS knobs shm@(SNat @m :$$ _) shn shp v0
  ( vars@(varm ::$ mrest)
  , Ast.AstLet varN uN
      (Ast.AstCond (AstLeqInt (AstConcreteK j)
                              (Ast.AstN1K NegateOp (AstIntVar varp))) i1 i2)
    :.$ prest )
  | varNameToAstVarId varm == varNameToAstVarId varp
  , - j + 1 <= 0 || - j + 1 >= valueOf @m
    || ixIsSmall prest && astIsSmall True uN =
    if | - j + 1 <= 0 ->
         astGatherKnobsS knobs shm shn shp
                         v0 (vars, Ast.AstLet varN uN i2 :.$ prest)
       | - j + 1 >= valueOf @m ->
         astGatherKnobsS knobs shm shn shp
                         v0 (vars, Ast.AstLet varN uN i1 :.$ prest)
       | otherwise ->
         withSNat (- j + 1) $ \(SNat @mj) ->
         gcastWith (unsafeCoerceRefl :: (mj <=? m) :~: True) $
         astLetFun v0 $ \v ->
         let varm2 = reboundsVarName (0, valueOf @mj - 1) varm
             varm3 = reboundsVarName (0, valueOf @m - valueOf @mj - 1) varm
         in astGatherKnobsS knobs (SNat @mj :$$ shsTail shm) shn shp v
              ( (::$) @mj varm2 mrest
              , substituteAstIxS (astVar varm2)
                                 varm (Ast.AstLet varN uN i1 :.$ prest) )
            `astAppendS`
            astGatherKnobsS knobs (SNat @(m - mj) :$$ shsTail shm) shn shp v
              ( (::$) @(m - mj) varm3 mrest
              , substituteAstIxS (AstConcreteK (- j + 1) + astVar varm3)
                                 varm (Ast.AstLet varN uN i2 :.$ prest))
astGatherKnobsS knobs
                shm@(SNat @m :$$ (_ :: ShS shmTail))
                shn
                shp@(SNat @p :$$ (_ :: ShS shpTail))
                v0
  ( varm ::$ mrest
  , AstIntVar varp :.$ prest )
  | knobPhase knobs `notElem` [PhaseVectorization, PhaseExpansion]
      -- prevent a loop
  , varm == varp
  , not (varm `varNameInIxS` prest)
  , FTKS _ x <- ftkAst v0 =
    withSNat (min (valueOf @p) (valueOf @m)) $ \(SNat @m2) ->
    gcastWith (unsafeCoerceRefl :: (m2 <=? p) :~: True) $
    gcastWith (unsafeCoerceRefl :: (m2 <=? m) :~: True) $
    Permutation.permFromListCont (permCycle
                                  $ shsLength (shsTail shm) + 1)
    $ \(permVars :: Permutation.Perm permVars) ->
    Permutation.permFromListCont (backpermCycle
                                  $ shsLength (shsTail shp) + 1)
    $ \(permIx :: Permutation.Perm permIx) ->
       gcastWith (unsafeCoerceRefl
                  :: m2 ': shmTail ++ shn
                     :~: Permutation.PermutePrefix
                           permVars (shmTail ++ (m2 ': shn))) $
       gcastWith (unsafeCoerceRefl
                  :: shpTail ++ (m2 ': shn)
                     :~: Permutation.PermutePrefix
                           permIx (m2 ': shpTail ++ shn)) $
       gcastWith (unsafeCoerceRefl
                  :: (Rank permVars <=? Rank (shmTail ++ (m2 ': shn)))
                     :~: True) $
       gcastWith (unsafeCoerceRefl
                  :: (Rank permIx <=? Rank (m2 ': shpTail ++ shn)) :~: True) $
       fromMaybe (error "astGatherKnobsS: impossible non-permutation")
       $ Permutation.permCheckPermutation permVars
       $ fromMaybe (error "astGatherKnobsS: impossible non-permutation")
       $ Permutation.permCheckPermutation permIx
       $ let v2 = astTransposeS permIx
                  $ astSliceS (SNat @0) (SNat @m2) (SNat @(p - m2)) v0
             u = astGatherKnobsS
                   knobs (shsTail shm) (SNat @m2 :$$ shn) (shsTail shp)
                   v2 (mrest, prest)
             ftk = FTKS (SNat @(m - m2) :$$ shsTail shm `shsAppend` shn) x
         in astTransposeS permVars u
            `astAppendS`
            fromPlain (astConcrete ftk (tdefTarget ftk))
astGatherKnobsS knobs shm@(m1' :$$ (shm4 :: ShS shm4)) shn shp
                v7@(Ast.AstFromVector _ (STKS _ x2) l)
                ( var4 ::$ vrest4
                , i4 :.$ rest4 )
  | knobPhase knobs `notElem` [PhaseVectorization, PhaseExpansion]
  , let g = case i4 of
          AstIntVar var | var == var4 -> Just id
          AstTimesK (AstConcreteK n) (AstIntVar var)
            | var == var4 -> Just (n *)
          -- TODO: add more or define evaluation
          _ -> Nothing
  , Just h <- g
  , ixIsSmall rest4 =
    let f i =
          let subRest4 = substituteAstIxS (AstConcreteK i) var4 rest4
              j = h i
          in if j >= V.length l
             then let FTKS _ x = ftkAst v7
                      ftk = FTKS (shsTail shm `shsAppend` shn) x
                  in fromPlain $ astConcrete ftk (tdefTarget ftk)
             else astGatherKnobsS knobs shm4 shn (shsTail shp)
                                  (l V.! j) (vrest4, subRest4)
    in astFromVector m1' (STKS (shsTail shm `shsAppend` shn) x2)
       $ V.fromListN (fromSNat' m1') $ map f [0 .. fromSNat' m1' - 1]
astGatherKnobsS knobs shm shn shp v0 (vars0, i1 :.$ rest1)
  | knobPhase knobs `notElem` [PhaseVectorization, PhaseExpansion]
      -- prevent a loop
  , not (Foldable.any (`varNameInAst` i1) vars0) =
    astGatherKnobsS
      knobs shm shn (shsTail shp)
      (astIndexKnobsS knobs (shsTail shp `shsAppend` shn) v0 (i1 :.$ ZIS))
      (vars0, rest1)
astGatherKnobsS knobs shm@(m :$$ _) shn shp v0
  (vars, ix@(i1 :.$ prest))
  | knobPhase knobs `notElem` [PhaseVectorization, PhaseExpansion]
      -- prevent a loop
  , let intInteresting = \case
          AstPlusK (AstConcreteK _) i2
            | Just (lb, _) <- intBounds i2
            , lb >= 0 -> True
          Ast.AstLet _ _ (AstPlusK (AstConcreteK _) i2)
            | Just (lb, _) <- intBounds i2
            , lb >= 0 -> True
          Ast.AstCond (AstLeqInt (AstConcreteK j) (AstIntVar var)) _ _
            | j <= 0 || j >= fromSNat' m || ixIsSmall prest
            , Foldable.any ((== varNameToAstVarId var)
                            . varNameToAstVarId) vars -> True
          Ast.AstCond (AstLeqInt (AstConcreteK j)
                                 (Ast.AstN1K NegateOp (AstIntVar var))) _ _
            | - j + 1 <= 0 || - j + 1 >= fromSNat' m || ixIsSmall prest
            , Foldable.any ((== varNameToAstVarId var)
                            . varNameToAstVarId) vars -> True
          Ast.AstLet _ uN
            (Ast.AstCond (AstLeqInt (AstConcreteK j) (AstIntVar var)) _ _)
            | j <= 0 || j >= fromSNat' m
              || ixIsSmall prest && astIsSmall True uN
            , Foldable.any ((== varNameToAstVarId var)
                            . varNameToAstVarId) vars -> True
          Ast.AstLet _ uN
            (Ast.AstCond (AstLeqInt (AstConcreteK j)
                                    (Ast.AstN1K NegateOp (AstIntVar var))) _ _)
            | - j + 1 <= 0 || - j + 1 >= fromSNat' m
              || ixIsSmall prest && astIsSmall True uN
            , Foldable.any ((== varNameToAstVarId var)
                            . varNameToAstVarId) vars -> True
          Ast.AstCond
            (Ast.AstBoolAndK
               (AstLeqInt (AstConcreteK j) (AstIntVar var)) _) _ _
            | j <= 0 || j >= fromSNat' m || ixIsSmall prest
            , Foldable.any ((== varNameToAstVarId var)
                            . varNameToAstVarId) vars -> True
          Ast.AstCond
            (Ast.AstBoolAndK
               (AstLeqInt (AstConcreteK j)
                          (Ast.AstN1K NegateOp (AstIntVar var))) _) _ _
            | - j + 1 <= 0 || - j + 1 >= fromSNat' m || ixIsSmall prest
            , Foldable.any ((== varNameToAstVarId var)
                            . varNameToAstVarId) vars -> True
          Ast.AstLet _ uN
            (Ast.AstCond
               (Ast.AstBoolAndK
                  (AstLeqInt (AstConcreteK j) (AstIntVar var)) _) _ _)
            | j <= 0 || j >= fromSNat' m
              || ixIsSmall prest && astIsSmall True uN
            , Foldable.any ((== varNameToAstVarId var)
                            . varNameToAstVarId) vars -> True
          Ast.AstLet _ uN
            (Ast.AstCond
               (Ast.AstBoolAndK
                  (AstLeqInt (AstConcreteK j)
                             (Ast.AstN1K NegateOp (AstIntVar var))) _) _ _)
            | - j + 1 <= 0 || - j + 1 >= fromSNat' m
              || ixIsSmall prest && astIsSmall True uN
            , Foldable.any ((== varNameToAstVarId var)
                            . varNameToAstVarId) vars -> True
          AstIntVar var
            | knobPhase knobs `elem` [PhaseSimplification, PhaseContraction]
            , null $ drop 1 $ filter (var `varNameInAst`) (Foldable.toList ix)
            , Foldable.any ((== varNameToAstVarId var)
                            . varNameToAstVarId) vars -> True
          ik | knobPhase knobs `elem` [PhaseSimplification, PhaseContraction]
             , not (Foldable.any (`varNameInAst` ik) vars) -> True
          -- We can't reorder ix for the gather(fromVector) rule above,
          -- because it becomes gather(transpose); we can only reorder vars.
          _ -> False
  , not (intInteresting i1)  -- now vars may need to be reordered, too
  , Just i <- findIndex intInteresting
                        (Foldable.toList ix) = assert (i > 0) $
    Permutation.permFromListCont (backpermCycle $ i + 1)
    $ \(perm :: Permutation.Perm perm) ->
    gcastWith (unsafeCoerceRefl
               :: Permutation.PermutePrefix perm (shp ++ shn)
                  :~: Permutation.PermutePrefix perm shp ++ shn) $
    gcastWith (unsafeCoerceRefl :: (Rank perm <=? Rank (shp ++ shn)) :~: True) $
    fromMaybe (error "astGatherKnobsS: impossible non-permutation")
    $ Permutation.permCheckPermutation perm
    $ let v2 = astTransposeS perm v0
      in astGatherKnobsS knobs shm shn (shsPermutePrefix perm shp)
                         v2 (vars, ixsPermutePrefix perm ix)
        -- this call is guaranteed to simplify as above, so the transpose
        -- won't reduce it back to the original and cause a loop
astGatherKnobsS knobs shm@(m :$$ _) shn shp v0
  (vars, ix@(i1 :.$ prest))
  | let varInteresting = \case
          Ast.AstCond (AstLeqInt (AstConcreteK j) (AstIntVar var)) _ _
            | j <= 0 || j >= fromSNat' m || ixIsSmall prest ->
              Just var
          Ast.AstCond (AstLeqInt (AstConcreteK j)
                                 (Ast.AstN1K NegateOp (AstIntVar var))) _ _
            | - j + 1 <= 0 || - j + 1 >= fromSNat' m || ixIsSmall prest ->
              Just var
          Ast.AstLet _ uN
            (Ast.AstCond (AstLeqInt (AstConcreteK j) (AstIntVar var)) _ _)
            | j <= 0 || j >= fromSNat' m
              || ixIsSmall prest && astIsSmall True uN ->
              Just var
          Ast.AstLet _ uN
            (Ast.AstCond (AstLeqInt (AstConcreteK j)
                                    (Ast.AstN1K NegateOp
                                                (AstIntVar var))) _ _)
            | - j + 1 <= 0 || - j + 1 >= fromSNat' m
              || ixIsSmall prest && astIsSmall True uN ->
              Just var
          Ast.AstCond
            (Ast.AstBoolAndK
               (AstLeqInt (AstConcreteK j) (AstIntVar var)) _) _ _
            | j <= 0 || j >= fromSNat' m || ixIsSmall prest ->
              Just var
          Ast.AstCond
            (Ast.AstBoolAndK
               (AstLeqInt (AstConcreteK j)
                          (Ast.AstN1K NegateOp (AstIntVar var))) _) _ _
            | - j + 1 <= 0 || - j + 1 >= fromSNat' m || ixIsSmall prest ->
              Just var
          Ast.AstLet _ uN
            (Ast.AstCond
               (Ast.AstBoolAndK
                  (AstLeqInt (AstConcreteK j) (AstIntVar var)) _) _ _)
            | j <= 0 || j >= fromSNat' m
              || ixIsSmall prest && astIsSmall True uN ->
              Just var
          Ast.AstLet _ uN
            (Ast.AstCond
               (Ast.AstBoolAndK
                  (AstLeqInt (AstConcreteK j)
                             (Ast.AstN1K NegateOp (AstIntVar var))) _) _ _)
            | - j + 1 <= 0 || - j + 1 >= fromSNat' m
              || ixIsSmall prest && astIsSmall True uN ->
              Just var
          AstIntVar var
            | knobPhase knobs `elem` [PhaseSimplification, PhaseContraction]
            , not (var `varNameInIxS` prest) -> Just var
          i4  -- has to be last, because ix can't be reordered
            | knobPhase knobs `elem` [PhaseSimplification, PhaseContraction]
            , Ast.AstFromVector{} <- v0
            , ixIsSmall prest
            , mvar <- case i4 of
                AstIntVar var -> Just var
                AstTimesK AstConcreteK{} (AstIntVar var) -> Just var
                _ -> Nothing
            , Just{} <- mvar -> mvar
          _ -> Nothing
  , Just varp <- varInteresting i1
  , Just i <- findIndex ((== varNameToAstVarId varp) . varNameToAstVarId)
                        (listsToList vars) = assert (i > 0) $
    Permutation.permFromListCont (backpermCycle $ i + 1)
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
    $ astGatherKnobsS knobs (shsPermutePrefix invperm shm) shn shp
                      v0 (listsPermutePrefix invperm vars, ix)
        -- this call is guaranteed to simplify as above, so the transpose
        -- won't reduce it back to the original and cause a loop
astGatherKnobsS knobs shm shn shp@(SNat @in1 :$$ (shp1' :: ShS shp1'))
                v4 (vars4, ix4@(i4 :.$ rest4))
  | FTKS _ x <- ftkAst v4 = case v4 of
    Ast.AstProject1{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstProject2{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    {- Ast.AstFromVector{} | gatherFromNF (shsTail shp) vars4 ix4 ->
        -- normal form
      Ast.AstGatherS @shm @shn @shp shn v4 (vars4, ix4) -}
    {- this rule seems counterproductive in many cases, so disabled until
       we can detect cases where it helps:
    Ast.AstFromVector snat STKS{} l ->
      -- Term rest4 is duplicated without sharing and we can't help it,
      -- because it needs to be in scope of vars4, so we can't use tlet.
      funToVarsIxS @shm shm $ \varsFresh (IxS !ixFresh) ->
        let f v = astGather @shm @shn @shp1' shn v (vars4, rest4)
            -- This subst doesn't currently break sharing because it's a rename.
            subst i =
              Foldable.foldr (\(i2, var2) v2 -> substituteAst i2 var2 v2)
                    i
                    (zipSizedS ixFresh vars4)
            i5 = subst i4
       in astGather @shm @shn @(p1' ': shm)
                    shn (astFromVector snat (STKS (shsFromListS varsFresh
                                                    `shsAppend` shn)
                                                   (ftkToSTK x))
                          $ V.map f l)
                    (varsFresh, i5 :.$ IxS ixFresh) -}
    Ast.AstFromVector{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    -- This accomplishes fusion if v is a gather or anything
    -- that gather can fuse with, but at the cost of an extra transpose
    -- that doesn't fuse here unless astTransposeAsGatherS is used.
    -- Since the transpose is O(1), let's leave this as is.
    Ast.AstSum snat@(SNat @n1) STKS{} v ->
      let perm3 = backpermCycle $ shsLength shp + 1
          perm4 = permCycle $ shsLength shm + 1
      in Permutation.permFromListCont perm3
         $ \(perm3S :: Permutation.Perm perm3P) ->
         gcastWith (unsafeCoerceRefl
                    :: Compare (Rank perm3P) (Rank (n1 : shp ++ shn))
                       :~: LT) $
         gcastWith (unsafeCoerceRefl
                    :: Permutation.PermutePrefix perm3P (n1 : (shp ++ shn))
                       :~: shp ++ (n1 : shn)) $
         fromMaybe (error "astGatherKnobsS: impossible non-permutation")
         $ Permutation.permCheckPermutation perm3S
         $ Permutation.permFromListCont perm4
         $ \(perm4S :: Permutation.Perm perm4P) ->
         gcastWith (unsafeCoerceRefl
                    :: Compare (Rank perm4P) (Rank (shm ++ (n1 : shn)))
                       :~: LT) $
         gcastWith (unsafeCoerceRefl
                    :: Permutation.PermutePrefix perm4P (shm ++ (n1 : shn))
                       :~: n1 : (shm ++ shn)) $
         fromMaybe (error "astGatherKnobsS: impossible non-permutation")
         $ Permutation.permCheckPermutation perm4S
         $ let innerGather =
                 astGather shm (snat :$$ shn) shp
                           (astTransposeS perm3S v) (vars4, ix4)
           in astSum snat (STKS (shm `shsAppend` shn) (ftkToSTK x))
              $ astTransposeS perm4S innerGather
                {- TODO: disabled until we can reliably fuse back to transpose
                if not (knobExpand knobs)
                then astTransposeS perm4S innerGather
                else astTransposeAsGatherS knobs perm4S innerGather -}
    Ast.AstReplicate _ STKS{} v ->
      let ftk = FTKS (shm `shsAppend` shn) x
          defArr = fromPlain $ astConcrete ftk (tdefTarget ftk)
      -- This boolean term may have free variables that act as universally
      -- quantified.
      in case 0 <=. i4 &&* i4 <=. valueOf @in1 - 1 of
        AstConcreteK b ->
          if b
          then astGather shm shn shp1' v (vars4, rest4)
          else defArr
        _ -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstReplicate (SNat @k) STKScalar v | ZIS <- rest4 ->
      let ftk = FTKS (shm `shsAppend` shn) x
          defArr = fromPlain $ astConcrete ftk (tdefTarget ftk)
      in case 0 <=. i4 &&* i4 <=. valueOf @k - 1 of
        AstConcreteK b ->
          if b then astGather shm shn shp1'
                              (astConvUpSFromK v) (vars4, rest4) else defArr
        _ -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstApply{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstVar{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstCond b v w | ixIsSmall ix4 ->
      astCond b (astGather shm shn shp v (vars4, ix4))
                (astGather shm shn shp w (vars4, ix4))
    Ast.AstCond{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstBuild1{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    AstConcreteS{} -> case unRepl1 v4 of
      Just u ->
        let ftk = FTKS (shm `shsAppend` shn) x
            defArr = fromPlain $ astConcrete ftk (tdefTarget ftk)
        in case 0 <=. i4 &&* i4 <=. valueOf @in1 - 1 of
          AstConcreteK b ->
            if b
            then astGather shm shn shp1' u (vars4, rest4)
            else defArr
          _ -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
      _ -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
             -- free variables possible in the index, so can't compute the array

    Ast.AstLet var u v ->
      astLet var u (astGather shm shn shp v (vars4, ix4))

    Ast.AstPrimalPart{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstDualPart{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstPlainPart{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstFromPrimal v ->
      fromPrimal $ astGather shm shn shp v (vars4, ix4)
    Ast.AstFromDual v ->
      fromDual $ astGather shm shn shp v (vars4, ix4)
    Ast.AstFromPlain v ->
      fromPlain $ astGather shm shn shp v (vars4, ix4)

    -- Going inside a binary ops usually makes a term more expensive
    -- to interpret and inverting that requires comparing two arguments,
    -- so it's not practical.
    AstPlusS{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    AstTimesS{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstN1S{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstR1S{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstR2S{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstI2S{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstFloorS{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstFromIntegralS{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstCastS{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstArgMinS @n @sh v -> case ftkAst v of
     FTKS nsh _ -> case shsLast nsh of
      nl@(SNat @nl) ->
        let shnl = shn `shsAppend` (nl :$$ ZSS)
        in gcastWith (unsafeCoerceRefl
                     :: shp ++ (shn ++ '[nl]) :~: n ': sh) $
           gcastWith (unsafeCoerceRefl
                      :: Head (shm ++ (shn ++ '[nl]))
                         ': Tail (shm ++ (shn ++ '[nl]))
                         :~: shm ++ (shn ++ '[nl])) $
           gcastWith (unsafeCoerceRefl
                      :: Init (shm ++ (shn ++ '[nl]))
                      :~: shm ++ shn) $
           Ast.AstArgMinS @(Head (shm ++ (shn ++ '[nl])))
                          @(Tail (shm ++ (shn ++ '[nl])))
           $ astGather shm shnl shp v (vars4, ix4)
    Ast.AstArgMaxS @n @sh v -> case ftkAst v of
     FTKS nsh _ -> case shsLast nsh of
      nl@(SNat @nl) ->
        let shnl = shn `shsAppend` (nl :$$ ZSS)
        in gcastWith (unsafeCoerceRefl
                     :: shp ++ (shn ++ '[nl]) :~: n ': sh) $
           gcastWith (unsafeCoerceRefl
                      :: Head (shm ++ (shn ++ '[nl]))
                         ': Tail (shm ++ (shn ++ '[nl]))
                         :~: shm ++ (shn ++ '[nl])) $
           gcastWith (unsafeCoerceRefl
                      :: Init (shm ++ (shn ++ '[nl]))
                      :~: shm ++ shn) $
           Ast.AstArgMaxS @(Head (shm ++ (shn ++ '[nl])))
                          @(Tail (shm ++ (shn ++ '[nl])))
           $ astGather shm shnl shp v (vars4, ix4)

    {- is reverted in astGatherKnobsS immediatedly; only do in expansion phase?
    Ast.AstIndexS @shm2 _shn2 v2 (i2 :.$ ZIS) ->
        astGather @shm @shn @(shm2 ++ shp) shn v2 (vars4, i2 :.$ ix4) -}
    Ast.AstIndexS{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstScatterS shm7 shn7 shp7 v (vars, AstIntVar var5 :.$ ix2)
      | AstIntVar var6 <- i4, var6 == var5 ->
        astGather shm shn (shsTail shp)
                  (astScatterS shm7 shn7 (shsTail shp7) v (vars, ix2))
                  (vars4, rest4)
    Ast.AstScatterS{} ->  -- normal form
      Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstGatherS @shm2 @shn2 @shp2 shm2 shn2 shp2 v2 (vars2, ix2)
                   | SNat @rank4 <- ixsRank ix4
                   , SNat @rank2 <- listsRank vars2 ->
      let subst :: AstIxS AstMethodLet shm7 -> AstVarListS shm7
                -> AstInt AstMethodLet
                -> AstInt AstMethodLet
          subst (IxS ix) vars t0 =
            foldr (\ (v, i) -> substituteAst i v)
                  t0 (listsZip vars ix)
          inBounds :: AstIxS AstMethodLet shm7 -> AstVarListS shm7 -> Bool
          inBounds (IxS ix) vars =
            let inb (v, i) | Just (lbv, ubv) <- varNameToBounds v
                           , Just (lbi, ubi) <- intBounds i =
                  lbv <= lbi && ubi <= ubv
                inb _ = True
            in all inb (listsZip vars ix)
          composedGather ::  -- rank4 <= rank2
            Maybe (AstTensor AstMethodLet s (TKS2 (shm ++ shn) r))
          composedGather | SNat <- shsRank shm =
            -- we have: shm2 ++ shn2 == shp ++ shn
            -- so from ranks:
            gcastWith (unsafeCoerceRefl :: Take (Rank shp) shm2 :~: shp) $
            -- and from congruence:
--            gcastWith (unsafeCoerceRefl
--                       :: Drop (Rank shp) shm2 ++ shn2 :~: shn) $
            -- from congruence:
            gcastWith (unsafeCoerceRefl
                       :: (shm ++ Drop (Rank shp) shm2) ++ shn2
                          :~: shm ++ shn) $
            withKnownShS (shsDrop @(Rank shp) shm2) $
            withKnownShS shp $
            let vars2p = listsTake @(Rank shp) vars2
                vars22 = listsDrop @(Rank shp) vars2
                ix22 = fmap (subst ix4 vars2p) ix2
                list422 = vars4 `listsAppend` vars22
            in if ixIsSmall ix4 && inBounds ix4 vars2p
               then Just $ astGather (shm `shsAppend` shsDrop @(Rank shp) shm2)
                                     shn2
                                     shp2
                                     v2 (list422, ix22)
               else Nothing
          assimilatedGather ::  -- rank2 <= rank4
            Maybe (AstTensor AstMethodLet s (TKS2 (shm ++ shn) r))
          assimilatedGather | SNat <- shsRank shm =
            -- we have: shm2 ++ shn2 == shp ++ shn
            -- so from ranks:
            gcastWith (unsafeCoerceRefl :: Take (Rank shm2) shp :~: shm2) $
            -- and from congruence:
--            gcastWith (unsafeCoerceRefl
--                       :: Drop (Rank shm2) shp ++ shn :~: shn2) $
            -- from congruence:
            gcastWith (unsafeCoerceRefl
                       :: (shp2 ++ Drop (Rank shm2) shp) ++ shn
                          :~: shp2 ++ shn2) $
            withKnownShS (shsDrop @(Rank shm2) shp) $
            withKnownShS shm2 $
            let ix42 = ixsTake @(Rank shm2) ix4
                ix44 = ixsDrop @(Rank shm2) ix4
                ix22 = fmap (subst ix42 vars2) ix2
                ix2244 = ix22 `ixsAppend` ix44
            in if ixIsSmall ix42 && inBounds ix42 vars2
               then Just $ astGather shm
                                     shn
                                     (shp2 `shsAppend` shsDrop @(Rank shm2) shp)
                                     v2 (vars4, ix2244)
               else Nothing
      in fromMaybe (Ast.AstGatherS shm shn shp v4 (vars4, ix4))
         $ case cmpNat (Proxy @rank4) (Proxy @rank2) of
        LTI -> composedGather
        EQI -> assimilatedGather
        GTI -> gcastWith (flipCompare (Proxy @rank4) (Proxy @rank2))
                         assimilatedGather
    Ast.AstIotaS{} ->  -- probably nothing can be simplified; a normal form
      Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstAppendS{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
      -- fusing would result in gather([gather, gather]), so no gain
    Ast.AstSliceS{}-> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
      -- slicing is O(1) so no point fusing and complicating the expression;
      -- if it did not simplify further with slice, it wouldn't with gather
    Ast.AstReverseS{}-> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
      -- reversing is O(1)
    Ast.AstTransposeS @perm @sh perm v | FTKS sh _ <- ftkAst v ->
     if knobPhase knobs `notElem` [PhaseVectorization, PhaseExpansion]
     then Ast.AstGatherS shm shn shp v4 (vars4, ix4)
     else
      let rankPerm = Permutation.permRank perm
      in case gcompare (ixsRank ix4) rankPerm of
        GLT ->  -- TODO: this does not provide any proof, so use cmpNat :(
          astGather shm shn shp
                    (astTransposeAsGatherS knobs perm v) (vars4, ix4)
        _ ->
          gcastWith (lemRankMapJust $ shsTakeLen perm sh) $
          gcastWith (unsafeCoerceRefl :: Rank (TakeLen perm sh) :~: Rank perm) $
          permInverse perm
          $ \(invperm :: Nested.Perm invperm) proof ->
            case proof (ssxFromShX $ shxFromShS $ shsTakeLen perm sh) of
              Refl ->
                -- from PermutePrefix and ranks:
                gcastWith
                  (unsafeCoerceRefl
                   :: Permutation.PermutePrefix invperm shp ++ shn
                      :~: Permutation.PermutePrefix invperm (shp ++ shn)) $
                -- from AstTransposeS:
--                gcastWith
--                  (unsafeCoerceRefl
--                   :: Permutation.PermutePrefix invperm (shp ++ shn)
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
                in astGather shm shn (shsPermutePrefix invperm shp) v (vars4, invix4)
    Ast.AstReshapeS sh v ->
      if shsLength sh <= 1
      then astGather shm shn shp
                     (astReshapeAsGatherS knobs sh v) (vars4, ix4)
      else Ast.AstGatherS shm shn shp v4 (vars4, ix4)

    AstConvUp ftkz v -> case matchingFTK (ftkAst v) ftkz of
      Just Refl -> astGather shm shn shp v (vars4, ix4)
        -- rare, usually simplifies away earlier
      Nothing -> error "astGatherKnobsS: wrong tensor kinds in AstConvUp"
    -- These conversions need to stay down.
    Ast.AstConvert{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)

    -- These should not appear here unless via wacky tests.
    Ast.AstDot1InS{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstMatmul2S{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)

    Ast.AstBoolNotS{} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstBoolAndS {} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
    Ast.AstLeqS {} -> Ast.AstGatherS shm shn shp v4 (vars4, ix4)
 where
  astGather
    :: forall shm' shn' shp' s' r'. KnownSpan s'
    => ShS shm' -> ShS shn' -> ShS shp'
    -> AstTensor AstMethodLet s' (TKS2 (shp' ++ shn') r')
    -> (AstVarListS shm', AstIxS AstMethodLet shp')
    -> AstTensor AstMethodLet s' (TKS2 (shm' ++ shn') r')
  astGather shm' shn' shp' v2 (vars2, ix2) =
    astGatherKnobsS knobs shm' shn' shp' v2 (vars2, ix2)

-- Normal form of chains of appends has the append constructor on the right.
astAppendS :: KnownSpan s
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
  fromPrimal $ astAppendS u v
astAppendS (Ast.AstFromDual u) (Ast.AstFromDual v) =
  fromDual $ astAppendS u v
astAppendS (Ast.AstFromPlain u) (Ast.AstFromPlain v) =
  fromPlain $ astAppendS u v
astAppendS (AstConcreteS u) (AstConcreteS v) =
  astConcreteS (tsappend (Concrete u) (Concrete v))
astAppendS (AstConcreteS u) (Ast.AstAppendS (AstConcreteS v) w) =
  astAppendS (astConcreteS (tsappend (Concrete u) (Concrete v))) w
astAppendS (Ast.AstAppendS v u) w = astAppendS v (astAppendS u w)
astAppendS u v = Ast.AstAppendS u v

astSliceS :: forall i n k sh s r. KnownSpan s
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
astSliceS SNat SNat SNat (Ast.AstGatherS shm shn shp v (var ::$ vars, ix)) =
  let varn = reboundsVarName (0, valueOf @n - 1) var
      ivar = valueOf @i + astVar varn
      ix2 = substituteAstIxS ivar var ix  -- cheap subst, because ivar is tiny
  in astGatherS (SNat @n :$$ shsTail shm) shn shp v (varn ::$ vars, ix2)
astSliceS i n@(SNat @n0) _k (Ast.AstAppendS v1 v2)
  | FTKS (m1@(SNat @m1) :$$ _) _ <- ftkAst v1
  , FTKS (m2@(SNat @m2) :$$ _) _ <- ftkAst v2 =
    let i1 = fromSNat' i `min` fromSNat' m1
        n1 = fromSNat' n `min` (fromSNat' m1 - i1)
        k1 = fromSNat' m1 - i1 - n1
        i2' = fromSNat' i `max` fromSNat' m1
        i2 = i2' - fromSNat' m1
        n2 = fromSNat' n - n1
        k2 = fromSNat' m2 - i2 - n2
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
-- This enlarges the term and increases computation, but sometimes
-- it permits eliminating the AstFromVector node altogether, so we risk it
-- for cases that commonly emerge from conditionals.
astSliceS i n@SNat k (Ast.AstTransposeS
                        perm@(SNat' @1 `PCons` SNat' @0 `PCons` PNil)
                        (Ast.AstFromVector (SNat' @2) (STKS (_ :$$ sh) x) l)) =
    Ast.AstTransposeS perm
    $ astFromVector (SNat @2) (STKS (n :$$ sh) x) (V.map (astSliceS i n k) l)
-- TODO: generalize (maybe the above, too) using unReplN, but it's hard.
-- TODO: does it really work only for replicate-like things in-between?
astSliceS i n@SNat k
          (Ast.AstTransposeS perm@(SNat' @1 `PCons` SNat' @0 `PCons` PNil) t)
  | STKS (snat :$$ _ :$$ sh3) x <- ftkToSTK $ ftkAst t
  , Just u <- unRepl1 t =
    astTransposeS perm
    $ astReplicate snat (STKS (n :$$ sh3) x)
    $ astSliceS i n k u
astSliceS i n k v1 = case v1 of
  Ast.AstCond b a2 a3 -> astCond b (astSliceS i n k a2) (astSliceS i n k a3)
  Ast.AstLet var u v -> astLet var u (astSliceS i n k v)
  Ast.AstFromPrimal v -> fromPrimal $ astSliceS i n k v
  Ast.AstFromDual v -> fromDual $ astSliceS i n k v
  Ast.AstFromPlain v -> fromPlain $ astSliceS i n k v
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
  AstConcreteS v -> astConcreteS (tsslice i n k $ Concrete v)
  _ -> Ast.AstSliceS i n k v1

astReverseS :: forall n sh s r. KnownSpan s
            => AstTensor AstMethodLet s (TKS2 (n ': sh) r)
            -> AstTensor AstMethodLet s (TKS2 (n ': sh) r)
astReverseS (Ast.AstFromVector snat stk l) =
  astFromVector snat stk $ V.reverse l
astReverseS (Ast.AstReplicate snat stk v) = astReplicate snat stk v
astReverseS (Ast.AstCond b a2 a3) = astCond b (astReverseS a2) (astReverseS a3)
astReverseS (Ast.AstLet var u v) = astLet var u (astReverseS v)
astReverseS (Ast.AstFromPrimal v) = fromPrimal $ astReverseS v
astReverseS (Ast.AstFromDual v) = fromDual $ astReverseS v
astReverseS (Ast.AstFromPlain v) = fromPlain $ astReverseS v
astReverseS (Ast.AstGatherS shm@(SNat @k :$$ _) shn shp v (var ::$ vars, ix)) =
  let ivar = valueOf @k - astVar var
      ix2 = substituteAstIxS ivar var ix  -- cheap subst, because ivar is tiny
  in astGatherS shm shn shp v (var ::$ vars, ix2)
astReverseS (Ast.AstReverseS v) = v
astReverseS (Ast.AstTransposeS perm@(SNat' @1 `PCons` SNat' @0 `PCons` PNil) t)
  | STKS (snat :$$ sh2@(_ :$$ _)) x <- ftkToSTK $ ftkAst t
  , Just u <- unRepl1 t =
    astTransposeS perm
    $ astReplicate snat (STKS sh2 x)
    $ astReverseS u
astReverseS (AstConcreteS v) = astConcreteS (tsreverse $ Concrete v)
astReverseS v = Ast.AstReverseS v

-- TODO: try to completely cover the AstGatherS case here, which would permit
-- not expanding to astTransposeAsGatherS in astGatherCase
-- | Beware, this does not do full simplification, which often requires
-- the gather form, so astTransposeAsGather needs to be called in addition
-- if full simplification is required.
astTransposeS
  :: forall perm sh s r.
     (Permutation.IsPermutation perm, Rank perm <= Rank sh, KnownSpan s)
  => Permutation.Perm perm -> AstTensor AstMethodLet s (TKS2 sh r)
  -> AstTensor AstMethodLet s (TKS2 (Permutation.PermutePrefix perm sh) r)
astTransposeS perm t =
  gcastWith (unsafeCoerceRefl
             :: TakeLen perm sh ++ DropLen perm sh :~: sh) $ case perm of
 PNil -> t
 PCons (SNat' @0) PNil ->
   gcastWith (unsafeCoerceRefl :: Permutation.PermutePrefix '[0] sh :~: sh) $
   t
 _ | FTKS sh _ <- ftkAst t
   , Just u2 <- unReplN @_ @_ @(DropLen perm sh) (shsTakeLen perm sh) t ->
   astReplicateNS (shsPermute perm (shsTakeLen perm sh)) u2
 _ -> case t of
  Ast.AstFromVector snat@(SNat @n) (STKS @sh2 sh2 x) l
    | SNat' @0 `PCons` _ <- perm -> case permUnShift1 perm of
      (perm2 :: Permutation.Perm perm2) ->
        fromMaybe (error "astTransposeS: impossible non-permutation")
        $ Permutation.permCheckPermutation perm2
        $ gcastWith (unsafeCoerceRefl :: Rank perm2 + 1 :~: Rank perm)
        -- for GHC 9.10 only:
        $ gcastWith (unsafeCoerceRefl :: (Rank perm2 <=? Rank sh2) :~: True)
        $ gcastWith (unsafeCoerceRefl
                     :: Permutation.PermutePrefix perm (n : sh2)
                        :~: n : Permutation.PermutePrefix perm2 sh2)
        $ astFromVector snat (STKS (shsPermutePrefix perm2 sh2) x)
                        (V.map (astTransposeS perm2) l)
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
  _ | SNat' @0 `PCons` _ <- perm
    , STKS ((:$$) @n @sh2 snat sh2) x <- ftkToSTK $ ftkAst t
    , Just u <- unRepl1 t -> case permUnShift1 perm of
      (perm2 :: Permutation.Perm perm2) ->
        fromMaybe (error "astTransposeS: impossible non-permutation")
        $ Permutation.permCheckPermutation perm2
        $ gcastWith (unsafeCoerceRefl :: Rank perm2 + 1 :~: Rank perm)
        -- for GHC 9.10 only:
        $ gcastWith (unsafeCoerceRefl :: (Rank perm2 <=? Rank sh2) :~: True)
        $ gcastWith (unsafeCoerceRefl
                     :: Permutation.PermutePrefix perm (n : sh2)
                        :~: n : Permutation.PermutePrefix perm2 sh2)
        $ astReplicate snat (STKS (shsPermutePrefix perm2 sh2) x)
                       (astTransposeS perm2 u)
  -- This increases term size and work, so limited to size 2.
  Ast.AstReplicate snat1@SNat _
                   (Ast.AstFromVector snat2@(SNat' @2) stk2@STKScalar l)
    | SNat' @1 `PCons` SNat' @0 `PCons` PNil <- perm ->
      astFromVector snat2 (STKS (snat1 :$$ ZSS) stk2)
                    (V.map (astReplicate snat1 stk2) l)
  -- TODO: generalize
  Ast.AstReplicate snat1@SNat _
                   (Ast.AstFromVector snat2@(SNat' @2) stk2@(STKS sh x) l)
    | SNat' @1 `PCons` SNat' @0 `PCons` PNil <- perm ->
      astFromVector snat2 (STKS (snat1 :$$ sh) x)
                    (V.map (astReplicate snat1 stk2) l)
  Ast.AstCond b u v -> astCond b (astTransposeS perm u) (astTransposeS perm v)

  Ast.AstLet var u v -> astLet var u (astTransposeS perm v)

  Ast.AstFromPrimal v -> fromPrimal $ astTransposeS perm v
  Ast.AstFromDual v -> fromDual $ astTransposeS perm v
  Ast.AstFromPlain v -> fromPlain $ astTransposeS perm v

  AstPlusS u v -> astTransposeS perm u + astTransposeS perm v
  AstTimesS u v -> astTransposeS perm u * astTransposeS perm v
  Ast.AstN1S NegateOp u -> negate (astTransposeS perm u)
  Ast.AstN1S AbsOp u -> abs (astTransposeS perm u)
  Ast.AstN1S SignumOp u -> signum (astTransposeS perm u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astTransposeS perm u)
  Ast.AstR2S opCode u v ->
    Ast.AstR2S opCode (astTransposeS perm u) (astTransposeS perm v)
  Ast.AstI2S opCode u v ->
    Ast.AstI2S opCode (astTransposeS perm u) (astTransposeS perm v)
  AstConcreteS v -> astConcreteS (tstranspose perm $ Concrete v)
--  Ast.AstFloorS v -> astFloorS $ astTransposeS perm v
--  Ast.AstFromIntegralS v -> astFromIntegralS $ astTransposeS perm v
--  Ast.AstCastS v -> astCastS $ astTransposeS perm v

  Ast.AstIndexS @shm shn v ix | n <- ixsRank ix ->
    Permutation.permFromListCont
      (Permutation.permToList'
       $ iterate (unsafeCoerce Permutation.permShift1) perm
         !! (fromSNat' n))  -- this has a fake type, but that's fine
      $ \ (permn :: Perm permn) ->
        fromMaybe (error "astTransposeS: impossible non-permutation")
        $ Permutation.permCheckPermutation permn
        $ gcastWith (unsafeCoerceRefl
                     :: Permutation.PermutePrefix permn (shm ++ sh)
                        :~: shm ++ Permutation.PermutePrefix perm sh)
-- should suffice, but it doesn't
--      $ gcastWith (unsafeCoerceRefl :: Rank permn :~: n + Rank perm)
        $ gcastWith (unsafeCoerceRefl
                     :: (Rank permn <=? Rank (shm ++ sh)) :~: True)
        $ astIndexS (shsPermutePrefix perm shn) (astTransposeS permn v) ix
  Ast.AstScatterS @_ @shn @shp shm shn shp v (vars, ix)
    -- TODO: should the below be backpermute or permute?
    | gcompare (Permutation.permRank perm) (ixsRank ix) /= GGT ->
        let ix2 :: AstIxS AstMethodLet (Permutation.PermutePrefix perm shp)
            ix2 = ixsPermutePrefix perm ix
        in gcastWith (unsafeCoerceRefl
                      :: Permutation.PermutePrefix perm shp ++ shn
                         :~: Permutation.PermutePrefix perm (shp ++ shn)) $
           astScatterS shm shn (shsPermutePrefix perm shp)
                       v (vars, ix2)
  Ast.AstGatherS @shm @shn shm shn shp v (vars, ix)
    -- TODO: should the below be backpermute or permute?
    | gcompare (Permutation.permRank perm) (listsRank vars) /= GGT ->
        let vars2 :: AstVarListS (Permutation.PermutePrefix perm shm)
            vars2 = listsPermutePrefix perm vars
        in gcastWith (unsafeCoerceRefl
                      :: Permutation.PermutePrefix perm shm ++ shn
                         :~: Permutation.PermutePrefix perm (shm ++ shn)) $
           astGatherS (shsPermutePrefix perm shm) shn shp
                      v (vars2, ix)
  Ast.AstAppendS u v | SNat' @0 `PCons` _ <- perm
                     , FTKS ((:$$) @m @sh2 _ _) _ <- ftkAst u
                     , FTKS ((:$$) @n _ _) _ <- ftkAst v ->
    gcastWith (unsafeCoerceRefl
               :: Permutation.PermutePrefix perm ((m + n) : sh2)
                  :~: m + n : Tail (Permutation.PermutePrefix
                                      perm (m : sh2))) $
    gcastWith (unsafeCoerceRefl
               :: Permutation.PermutePrefix perm ((m + n) : sh2)
                  :~: m + n : Tail (Permutation.PermutePrefix
                                      perm (n : sh2))) $
    astAppendS (astTransposeS perm u) (astTransposeS perm v)
  Ast.AstSliceS i n@(SNat @n) k u | SNat' @0 `PCons` _ <- perm
                                  , FTKS ((:$$) @ink @sh2 _ _) _ <- ftkAst u ->
    gcastWith (unsafeCoerceRefl
               :: Permutation.PermutePrefix perm (n : sh2)
                  :~: n : Tail (Permutation.PermutePrefix perm (ink : sh2))) $
    astSliceS i n k (astTransposeS perm u)
  Ast.AstReverseS u | SNat' @0 `PCons` _ <- perm ->
    astReverseS (astTransposeS perm u)
  Ast.AstTransposeS @_ @sh2 perm2 u | FTKS sh2 _ <- ftkAst u ->
    -- TODO: try to perform at type level
    let permV = Permutation.permToList' perm
        perm2V = Permutation.permToList' perm2
        perm2Matched =
          perm2V
          ++ take (length permV - length perm2V) (drop (length perm2V) [0 ..])
        perm3V = normalizePermutationHack
                 $ backpermutePrefixList permV perm2Matched
    in Permutation.permFromListCont perm3V $ \(perm3
                                               :: Permutation.Perm perm3) ->
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
astReshapeS :: forall sh sh2 x s. (Product sh ~ Product sh2, KnownSpan s)
            => ShS sh2 -> AstTensor AstMethodLet s (TKS2 sh x)
            -> AstTensor AstMethodLet s (TKS2 sh2 x)
astReshapeS sh2 t = case t of
  Ast.AstReplicate (SNat' @1) STKS{} x -> astReshapeS sh2 x
  _ | Just u <- unRepl t
    , Refl <- lemAppNil @sh2 -> astReplicateNS sh2 u
  _ | STKS ((:$$) @_ @sh1 k _) x <- ftkToSTK $ ftkAst t
    , Just u <- unRepl1 t
    , (:$$) @_ @rest2 k2 rest2 <- sh2
    , Just Refl <- testEquality k k2 ->
      gcastWith (unsafeCoerceRefl :: Product rest2 :~: Product sh1) $
      astReplicate k (STKS rest2 x) $ astReshapeS rest2 u
  Ast.AstLet var u v -> astLet var u (astReshapeS @_ @sh2 sh2 v)
  Ast.AstFromPrimal v -> fromPrimal $ astReshapeS sh2 v
  Ast.AstFromDual v -> fromDual $ astReshapeS sh2 v
  Ast.AstFromPlain v -> fromPlain $ astReshapeS sh2 v
  -- Reshaping can be costly, so we don't touch AstTimesS, etc.
  Ast.AstN1S NegateOp u -> negate (astReshapeS @_ @sh2 sh2 u)
  Ast.AstN1S AbsOp u -> abs (astReshapeS @_ @sh2 sh2 u)
  Ast.AstN1S SignumOp u -> signum (astReshapeS @_ @sh2 sh2 u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (astReshapeS @_ @sh2 sh2 u)
  Ast.AstReshapeS _ v -> astReshapeS @_ @sh2 sh2 v
  _ | FTKS sh _ <- ftkAst t -> case testEquality sh sh2 of
    Just Refl -> t
    _ -> Ast.AstReshapeS sh2 t

astConvert
  :: KnownSpan s
  => TKConversion y z -> AstTensor AstMethodLet s y
  -> AstTensor AstMethodLet s z
astConvert c a | yftk <- ftkAst a = case (yftk, convertFTK c yftk) of
  (_, zftk) | Just Refl <- matchingFTK yftk zftk -> a
    -- this covers the ConvId case and more, so not simplifying c at worst
    -- causes c to take more memory but doesn't inhibit rewriting
  -- Below we heavily depend on c being semantically determined
  -- by the domain and codomain. We pick the simplest such c.
  (FTKS ZSS (FTKScalar @rz), FTKScalar @ry)
    | Just Refl <- testEquality (typeRep @ry) (typeRep @rz) ->
      let c2 = ConvCmp ConvX0 ConvSX
      in astConvertDownKFromS c2 FTKScalar a
  (FTKScalar @ry, FTKS ZSS (FTKScalar @rz))
    | Just Refl <- testEquality (typeRep @ry) (typeRep @rz) ->
      let c2 = ConvCmp ConvXS (Conv0X STKScalar)
      in astConvertUp c2 (FTKS ZSS FTKScalar) a
  (FTKR shr xy, zftk@(FTKS sh xz))
    | Just Refl <- matchingFTK xy xz
    , Just Refl <- testEquality (shrRank shr) (shsRank sh) ->
      astConvertDownSFromR (convDown yftk (ftkToSTK zftk)) zftk a
  (FTKX shx xy, zftk@(FTKS sh xz))
    | Just Refl <- matchingFTK xy xz
    , Just Refl <- testEquality (shxRank shx) (shsRank sh) ->
      astConvertDownSFromX (convDown yftk (ftkToSTK zftk)) zftk a
  (_, zftk) | Just c2 <- convDownMaybe yftk (ftkToSTK zftk) ->
    astConvertDown c2 zftk a
  (_, zftk) | Just c2 <- convUpMaybe yftk zftk ->
    astConvertUp c2 zftk a
  _ -> case a of  -- normalize somewhat even for, e.g., product to product
    Ast.AstPrimalPart (Ast.AstConvert c2 a2) ->
      astPrimalPart $ astConvert (c `convCmp` c2) a2
    Ast.AstDualPart (Ast.AstConvert c2 a2) ->
      astDualPart $ astConvert (c `convCmp` c2) a2
    Ast.AstPlainPart (Ast.AstConvert c2 a2) ->
      astPlainPart $ astConvert (c `convCmp` c2) a2
    Ast.AstFromPrimal v -> fromPrimal $ astConvert c v
    Ast.AstFromDual v -> fromDual $ astConvert c v
    Ast.AstFromPlain v -> fromPlain $ astConvert c v
    Ast.AstConvert c2 t2 -> astConvert (c `convCmp` c2) t2
    _ -> Ast.AstConvert c a

-- We are pushing conversions to shaped tensors down, into concrete values
-- and towards variables, so that the conversions often cancel out.
astConvertDown :: forall y z s. KnownSpan s
               => TKConversion y z -> FullShapeTK z
               -> AstTensor AstMethodLet s y
               -> AstTensor AstMethodLet s z
astConvertDown c zftk t = case (ftkAst t, zftk) of
  (yftk, _) | Just Refl <- matchingFTK yftk zftk -> t
  (FTKS ZSS (FTKScalar @rz), FTKScalar @ry) ->
    case testEquality (typeRep @ry) (typeRep @rz) of
      Just Refl -> astConvertDownKFromS c FTKScalar t
      Nothing -> error "astConvertDown: tensor kinds don't match"
  (FTKR ZSR (FTKScalar @rz), FTKScalar @ry) ->
    case testEquality (typeRep @ry) (typeRep @rz) of
      Just Refl -> astConvertDownKFromR c t
      Nothing -> error "astConvertDown: tensor kinds don't match"
  (FTKX ZSX (FTKScalar @rz), FTKScalar @ry) ->
    case testEquality (typeRep @ry) (typeRep @rz) of
      Just Refl -> astConvertDownKFromX c t
      Nothing -> error "astConvertDown: tensor kinds don't match"
  (FTKR shr yx, FTKS shz zx)->
    case (matchingFTK yx zx, testEquality (shsRank shz) (shrRank shr)) of
      (Just Refl, Just Refl) -> astConvertDownSFromR c zftk t
      _ -> error "astConvertDown: tensor kinds don't match"
  (FTKX shy yx, FTKS shz zx) ->
    case (matchingFTK yx zx, testEquality (shsRank shz) (shxRank shy)) of
      (Just Refl, Just Refl) -> astConvertDownSFromX c zftk t
      _ -> error "astConvertDown: tensor kinds don't match"
  (FTKProduct yftk1 yftk2, _) -> case t of
    Ast.AstPair a1 a2 | FTKProduct zftk1 zftk2 <- zftk ->
      -- Here we can't always use the c the user presumably wrote,
      -- so we always create a canonical one.
      astPair (astConvertDown (convDown yftk1 (ftkToSTK zftk1)) zftk1 a1)
              (astConvertDown (convDown yftk2 (ftkToSTK zftk2)) zftk2 a2)
    Ast.AstLet var u v -> astLet var u (astConvertDown c zftk v)
    Ast.AstPrimalPart v -> astPrimalPart $ astConvertDown c zftk v
    Ast.AstDualPart v -> astDualPart $ astConvertDown c zftk v
    Ast.AstPlainPart v -> astPlainPart $ astConvertDown c zftk v
    Ast.AstFromPrimal v -> fromPrimal $ astConvertDown c zftk v
    Ast.AstFromDual v -> fromDual $ astConvertDown c zftk v
    Ast.AstFromPlain v -> fromPlain $ astConvertDown c zftk v
    Ast.AstConvert c2 t2 -> astConvert (c `convCmp` c2) t2
    _ -> Ast.AstConvert c t  -- don't introduce let just to push a conversion
  (yftk, _) ->
    error $ "astConvertDown: wrong tensor kinds: " ++ show (yftk, zftk, t)

astConvertDownKFromS
  :: KnownSpan s
  => TKConversion (TKS '[] r) (TKScalar r)
  -> FullShapeTK (TKScalar r) -> AstTensor AstMethodLet s (TKS '[] r)
  -> AstTensor AstMethodLet s (TKScalar r)
astConvertDownKFromS c (FTKScalar @r1) a = case a of
  Ast.AstProject1{} -> Ast.AstConvert c a
  Ast.AstProject2{} -> Ast.AstConvert c a
  Ast.AstSum snat (STKS ZSS (STKScalar @r2)) v
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      astSum snat STKScalar v
  Ast.AstSum{} -> error "astConvertDownKFromS: impossible"
  Ast.AstApply (AstLambda !var !v) ll ->
    astApply (AstLambda var (astConvertDownKFromS c FTKScalar v)) ll
  Ast.AstVar{} -> Ast.AstConvert c a
  Ast.AstCond b v1 v2 ->
    astCond b (astConvertDownKFromS c FTKScalar v1)
              (astConvertDownKFromS c FTKScalar v2)
  Ast.AstLet var u v ->
    astLet var u (astConvertDownKFromS c FTKScalar v)
  Ast.AstPrimalPart v ->
    astPrimalPart $ astConvertDownKFromS c FTKScalar v
  Ast.AstDualPart v ->
    astDualPart $ astConvertDownKFromS c FTKScalar v
  Ast.AstPlainPart v ->
    astPlainPart $ astConvertDownKFromS c FTKScalar v
  AstPlusS @r2 u v
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      astConvertDownKFromS c FTKScalar u + astConvertDownKFromS c FTKScalar v
  AstPlusS{} -> error "astConvertDownKFromS: impossible"
  AstTimesS @r2 u v
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      astConvertDownKFromS c FTKScalar u * astConvertDownKFromS c FTKScalar v
  AstTimesS{} -> error "astConvertDownKFromS: impossible"
  Ast.AstN1S @r2 NegateOp u
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      negate (astConvertDownKFromS c FTKScalar u)
  Ast.AstN1S @r2 AbsOp u
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      abs (astConvertDownKFromS c FTKScalar u)
  Ast.AstN1S @r2 SignumOp u
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      signum (astConvertDownKFromS c FTKScalar u)
  Ast.AstN1S{} -> error "astConvertDownKFromS: impossible"
  Ast.AstR1S @r2 opCode u
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      Ast.AstR1K opCode (astConvertDownKFromS c FTKScalar u)
  Ast.AstR1S{} -> error "astConvertDownKFromS: impossible"
  Ast.AstR2S @r2 opCode u v
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      Ast.AstR2K opCode (astConvertDownKFromS c FTKScalar u)
                        (astConvertDownKFromS c FTKScalar v)
  Ast.AstR2S{} -> error "astConvertDownKFromS: impossible"
  Ast.AstI2S @r2 QuotOp u v
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      astConvertDownKFromS c FTKScalar u
      `quotH` astConvertDownKFromS c FTKScalar v
  Ast.AstI2S @r2 RemOp u v
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      astConvertDownKFromS c FTKScalar u
      `remH` astConvertDownKFromS c FTKScalar v
  Ast.AstI2S{} -> error "astConvertDownKFromS: impossible"
  AstConcreteS @r2 v
    | ZSS <- Nested.sshape v
    , Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      AstConcreteK (Nested.sunScalar v)
  AstConcreteS{} -> error "astConvertDownKFromS: impossible"
  Ast.AstFloorS @_ @r2 v
    | FTKS ZSS FTKScalar <- ftkAst v
    , Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      astFloorK (astConvDownKFromS v)
  Ast.AstFloorS{} -> error "astConvertDownKFromS: impossible"
  Ast.AstFromIntegralS @_ @r2 v
    | FTKS ZSS FTKScalar <- ftkAst v
    , Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      astFromIntegralK (astConvDownKFromS v)
  Ast.AstFromIntegralS{} -> error "astConvertDownKFromS: impossible"
  Ast.AstCastS @_ @r2 v
    | FTKS ZSS FTKScalar <- ftkAst v
    , Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      astCastK (astConvDownKFromS v)
  Ast.AstCastS{} -> error "astConvertDownKFromS: impossible"
  Ast.AstArgMinS v
    | FTKS (_ :$$ ZSS) FTKScalar <- ftkAst v
    , Just Refl <- testEquality (typeRep @r1) (typeRep @Int) ->
      astArgMinK v
  Ast.AstArgMinS{} -> error "astConvertDownKFromS: impossible"
  Ast.AstArgMaxS v
    | FTKS (_ :$$ ZSS) FTKScalar <- ftkAst v
    , Just Refl <- testEquality (typeRep @r1) (typeRep @Int) ->
      astArgMaxK v
  Ast.AstArgMaxS{} -> error "astConvertDownKFromS: impossible"
  Ast.AstIndexS{} -> Ast.AstConvert c a  -- TODO, here and below
  Ast.AstScatterS{} -> Ast.AstConvert c a
  Ast.AstGatherS{} -> Ast.AstConvert c a
  Ast.AstTransposeS{} -> Ast.AstConvert c a
  Ast.AstReshapeS{} -> Ast.AstConvert c a
  Ast.AstDot1InS{} -> Ast.AstConvert c a
  Ast.AstBoolNotS{} -> Ast.AstConvert c a
  Ast.AstBoolAndS{} -> Ast.AstConvert c a
  Ast.AstLeqS{} -> Ast.AstConvert c a
  Ast.AstFromPrimal v -> fromPrimal $ astConvertDownKFromS c FTKScalar v
  Ast.AstFromDual v -> fromDual $ astConvertDownKFromS c FTKScalar v
  Ast.AstFromPlain v -> fromPlain $ astConvertDownKFromS c FTKScalar v
  Ast.AstConvert c2 a2 -> astConvert (c `convCmp` c2) a2

astConvertDownKFromR
  :: KnownSpan s
  => TKConversion (TKR 0 r) (TKScalar r)
  -> AstTensor AstMethodLet s (TKR 0 r)
  -> AstTensor AstMethodLet s (TKScalar r)
astConvertDownKFromR c a = case a of
  Ast.AstProject1{} -> Ast.AstConvert c a
  Ast.AstProject2{} -> Ast.AstConvert c a
  Ast.AstSum{} -> Ast.AstConvert c a  -- too complex and surely already done
  Ast.AstApply (AstLambda !var !v) ll ->
    astApply (AstLambda var (astConvertDownKFromR c v)) ll
  Ast.AstVar{} -> Ast.AstConvert c a
  Ast.AstCond b v1 v2 ->
    astCond b (astConvertDownKFromR c v1)
              (astConvertDownKFromR c v2)
  Ast.AstLet var u v ->
    astLet var u (astConvertDownKFromR c v)
  Ast.AstPrimalPart v ->
    astPrimalPart $ astConvertDownKFromR c v
  Ast.AstDualPart v ->
    astDualPart $ astConvertDownKFromR c v
  Ast.AstPlainPart v ->
    astPlainPart $ astConvertDownKFromR c v
  Ast.AstFromPrimal v -> fromPrimal $ astConvertDownKFromR c v
  Ast.AstFromDual v -> fromDual $ astConvertDownKFromR c v
  Ast.AstFromPlain v -> fromPlain $ astConvertDownKFromR c v
  Ast.AstConvert c2 a2 -> astConvert (c `convCmp` c2) a2

astConvertDownKFromX
  :: KnownSpan s
  => TKConversion (TKX '[] r) (TKScalar r)
  -> AstTensor AstMethodLet s (TKX '[] r)
  -> AstTensor AstMethodLet s (TKScalar r)
astConvertDownKFromX c a = case a of
  Ast.AstProject1{} -> Ast.AstConvert c a
  Ast.AstProject2{} -> Ast.AstConvert c a
  Ast.AstSum{} -> Ast.AstConvert c a  -- too complex and surely already done
  Ast.AstApply (AstLambda !var !v) ll ->
    astApply (AstLambda var (astConvertDownKFromX c v)) ll
  Ast.AstVar{} -> Ast.AstConvert c a
  Ast.AstCond b v1 v2 ->
    astCond b (astConvertDownKFromX c v1)
              (astConvertDownKFromX c v2)
  Ast.AstLet var u v ->
    astLet var u (astConvertDownKFromX c v)
  Ast.AstPrimalPart v ->
    astPrimalPart $ astConvertDownKFromX c v
  Ast.AstDualPart v ->
    astDualPart $ astConvertDownKFromX c v
  Ast.AstPlainPart v ->
    astPlainPart $ astConvertDownKFromX c v
  Ast.AstFromPrimal v -> fromPrimal $ astConvertDownKFromX c v
  Ast.AstFromDual v -> fromDual $ astConvertDownKFromX c v
  Ast.AstFromPlain v -> fromPlain $ astConvertDownKFromX c v
  Ast.AstConvert c2 a2 -> astConvert (c `convCmp` c2) a2

-- We are pushing conversions to shaped tensors down, into concrete values
-- and towards variables, so that the conversions often cancel out.
astConvertDownSFromR :: forall sh x s. KnownSpan s
                     => TKConversion (TKR2 (Rank sh) x) (TKS2 sh x)
                     -> FullShapeTK (TKS2 sh x)
                     -> AstTensor AstMethodLet s (TKR2 (Rank sh) x)
                     -> AstTensor AstMethodLet s (TKS2 sh x)
astConvertDownSFromR c zftk@(FTKS sh x) a0 = case a0 of
  Ast.AstConvert c2 a2 -> astConvert (c `convCmp` c2) a2
  Ast.AstProject1{} -> Ast.AstConvert c a0
  Ast.AstProject2{} -> Ast.AstConvert c a0
  -- TODO: here and elsewhere, make sure the generated c2 is unique/correct
  Ast.AstFromVector snat@SNat (STKR @n _ xstk) l -> case sh of
    snat2@SNat :$$ rest | Just Refl <- sameNat snat snat2
                        , Refl <- lemRankReplicate (Proxy @n) ->
      let c2 = convCmp (ConvXS' (FTKS rest x)) ConvRX
      in astFromVector snat (STKS rest xstk)
                       (V.map (astConvert c2) l)
    _ -> error "astConvertDownSFromR: impossible shape"
  Ast.AstSum snat@SNat (STKR @n _ xstk) a
    | Refl <- lemRankReplicate (Proxy @(1 + n)) ->
      let c2 = convCmp (ConvXS' (FTKS (snat :$$ sh) x)) ConvRX
          !a2 = astConvert c2 a
      in astSum snat (STKS sh xstk) a2
  Ast.AstReplicate snat@SNat (STKR @n _ xstk) a -> case sh of
    snat2@SNat :$$ rest | Just Refl <- sameNat snat snat2
                        , Refl <- lemRankReplicate (Proxy @n) ->
      let c2 = convCmp (ConvXS' (FTKS rest x)) ConvRX
          !a2 = astConvert c2 a
      in astReplicate snat (STKS rest xstk) a2
    _ -> error "astConvertDownSFromR: impossible shape"
  Ast.AstApply{} -> Ast.AstConvert c a0
  Ast.AstVar{} -> Ast.AstConvert c a0
  Ast.AstCond b v w -> astCond b (astConvertDownSFromR c zftk v)
                                 (astConvertDownSFromR c zftk w)
  Ast.AstBuild1 snat@SNat (STKR @n _ xstk) (var, a) -> case sh of
    snat2@SNat :$$ rest | Just Refl <- sameNat snat snat2
                        , Refl <- lemRankReplicate (Proxy @n) ->
      let c2 = convCmp (ConvXS' (FTKS rest x)) ConvRX
          !a2 = astConvert c2 a
      in Ast.AstBuild1 snat (STKS rest xstk) (var, a2)
    _ -> error "astConvertDownSFromR: impossible shape"
  Ast.AstLet var u v -> astLet var u (astConvertDownSFromR c zftk v)
  Ast.AstPrimalPart a -> astPrimalPart $ astConvertDownSFromR c zftk a
  Ast.AstDualPart a -> astDualPart $ astConvertDownSFromR c zftk a
  Ast.AstPlainPart a -> astPlainPart $ astConvertDownSFromR c zftk a
  Ast.AstFromPrimal a -> fromPrimal $ astConvertDownSFromR c zftk a
  Ast.AstFromDual a -> fromDual $ astConvertDownSFromR c zftk a
  Ast.AstFromPlain a -> fromPlain $ astConvertDownSFromR c zftk a

astConvertDownSFromX :: forall sh shx x s. (KnownSpan s, Rank shx ~ Rank sh)
                     => TKConversion (TKX2 shx x) (TKS2 sh x)
                     -> FullShapeTK (TKS2 sh x)
                     -> AstTensor AstMethodLet s (TKX2 shx x)
                     -> AstTensor AstMethodLet s (TKS2 sh x)
astConvertDownSFromX c zftk@(FTKS sh x) a0 = case a0 of
  Ast.AstConvert c2 a2 -> astConvert (c `convCmp` c2) a2
  Ast.AstProject1{} -> Ast.AstConvert c a0
  Ast.AstProject2{} -> Ast.AstConvert c a0
  Ast.AstFromVector snat@SNat (STKX @shx2 _ xstk) l -> case sh of
    (:$$) @_ @rest snat2@SNat rest | Just Refl <- sameNat snat snat2 ->
      -- This is needed only for GHC 9.10.
      gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank shx2) $
      let c2 = ConvXS' (FTKS rest x)
      in astFromVector snat (STKS rest xstk)
                       (V.map (astConvert c2) l)
    _ -> error "astConvertDownSFromX: impossible shape"
  Ast.AstSum snat@SNat (STKX _ xstk) a ->
      let c2 = ConvXS' (FTKS (snat :$$ sh) x)
          !a2 = astConvert c2 a
      in astSum snat (STKS sh xstk) a2
  Ast.AstReplicate snat@SNat (STKX @shx2 _ xstk) a -> case sh of
    (:$$) @_ @rest snat2@SNat rest | Just Refl <- sameNat snat snat2 ->
      -- This is needed only for GHC 9.10.
      gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank shx2) $
      let c2 = ConvXS' (FTKS rest x)
          !a2 = astConvert c2 a
      in astReplicate snat (STKS rest xstk) a2
    _ -> error "astConvertDownSFromX: impossible shape"
  Ast.AstApply{} -> Ast.AstConvert c a0
  Ast.AstVar{} -> Ast.AstConvert c a0
  Ast.AstCond b v w -> astCond b (astConvertDownSFromX c zftk v)
                                 (astConvertDownSFromX c zftk w)
  Ast.AstBuild1 snat@SNat (STKX @shx2 _ xstk) (var, a) -> case sh of
    (:$$) @_ @rest snat2@SNat rest | Just Refl <- sameNat snat snat2 ->
      -- This is needed only for GHC 9.10.
      gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank shx2) $
      let c2 = ConvXS' (FTKS rest x)
          !a2 = astConvert c2 a
      in Ast.AstBuild1 snat (STKS rest xstk) (var, a2)
    _ -> error "astConvertDownSFromX: impossible shape"
  Ast.AstLet var u v -> astLet var u (astConvertDownSFromX c zftk v)
  Ast.AstPrimalPart a -> astPrimalPart $ astConvertDownSFromX c zftk a
  Ast.AstDualPart a -> astDualPart $ astConvertDownSFromX c zftk a
  Ast.AstPlainPart a -> astPlainPart $ astConvertDownSFromX c zftk a
  Ast.AstFromPrimal a -> fromPrimal $ astConvertDownSFromX c zftk a
  Ast.AstFromDual a -> fromDual $ astConvertDownSFromX c zftk a
  Ast.AstFromPlain a -> fromPlain $ astConvertDownSFromX c zftk a

-- We are pulling conversions from shaped tensors up.
-- z is shaped or scalar or a product (presumably with some shaped components,
-- but it's not checked; the other components are supposed to be
-- converted identically, which is not checked in c, either).
astConvertUp
  :: KnownSpan s
  => TKConversion y z -> FullShapeTK z -> AstTensor AstMethodLet s y
  -> AstTensor AstMethodLet s z
astConvertUp c zftk t = case (ftkAst t, zftk, t) of
  (yftk, _, _) | Just Refl <- matchingFTK yftk zftk -> t
  -- Rare cases where we don't pull up but push down so that conversions
  -- don't end up interspersed with AstFromPrimal and similar.
  (_, _, Ast.AstPrimalPart (Ast.AstConvert c2 a2)) ->
    astPrimalPart $ astConvert (c `convCmp` c2) a2
  (_, _, Ast.AstDualPart (Ast.AstConvert c2 a2)) ->
    astDualPart $ astConvert (c `convCmp` c2) a2
  (_, _, Ast.AstPlainPart (Ast.AstConvert c2 a2)) ->
    astPlainPart $ astConvert (c `convCmp` c2) a2
  (_, _, Ast.AstFromPrimal v) ->
    fromPrimal $ astConvertUp c zftk v
  (_, _, Ast.AstFromDual v) ->
    fromDual $ astConvertUp c zftk v
  (_, _, Ast.AstFromPlain v )->
    fromPlain $ astConvertUp c zftk v
  (_, _, Ast.AstConvert c2 a2) ->
    astConvert (c `convCmp` c2) a2
  (FTKScalar @ry, FTKS ZSS (FTKScalar @rz), _) ->
    case testEquality (typeRep @ry) (typeRep @rz) of
      Just Refl -> Ast.AstConvert c t
      Nothing -> error "astConvertUp: tensor kinds don't match"
  (FTKScalar @ry, FTKR ZSR (FTKScalar @rz), _) ->
    case testEquality (typeRep @ry) (typeRep @rz) of
      Just Refl -> Ast.AstConvert c t
      Nothing -> error "astConvertUp: tensor kinds don't match"
  (FTKScalar @ry, FTKX ZSX (FTKScalar @rz), _) ->
    case testEquality (typeRep @ry) (typeRep @rz) of
      Just Refl -> Ast.AstConvert c t
      Nothing -> error "astConvertUp: tensor kinds don't match"
  (FTKS shz zx, FTKR shr yx, _) ->
    case (matchingFTK yx zx, testEquality (shsRank shz) (shrRank shr)) of
      (Just Refl, Just Refl) -> Ast.AstConvert c t
      _ -> error "astConvertUp: tensor kinds don't match"
  (FTKS shz zx, FTKX shy yx, _) ->
    case (matchingFTK yx zx, testEquality (shsRank shz) (shxRank shy)) of
      (Just Refl, Just Refl) -> Ast.AstConvert c t
      _ -> error "astConvertUp: tensor kinds don't match"
  (FTKProduct{}, _, _) -> Ast.AstConvert c t
  (yftk, _, _) ->
    error $ "astConvertUp: wrong tensor kinds: " ++ show (yftk, zftk, t)

astConvDown :: forall y z s. KnownSpan s
            => SingletonTK z -> AstTensor AstMethodLet s y
            -> AstTensor AstMethodLet s z
astConvDown zstk t = astConvert (convDown (ftkAst t) zstk) t

astConvDownKFromS :: forall r s. (KnownSpan s, GoodScalar r)
                  => AstTensor AstMethodLet s (TKS2 '[] (TKScalar r))
                  -> AstTensor AstMethodLet s (TKScalar r)
astConvDownKFromS t = astConvertDownKFromS (ConvCmp ConvX0 ConvSX) FTKScalar t

astConvDownSFromR :: forall sh s r. KnownSpan s
                  => ShS sh -> AstTensor AstMethodLet s (TKR2 (Rank sh) r)
                  -> AstTensor AstMethodLet s (TKS2 sh r)
astConvDownSFromR sh t = case ftkAst t of
  FTKR _ x | Refl <- lemRankReplicate (Proxy @(Rank sh)) ->
    let zftk = FTKS sh x
    in astConvertDownSFromR (ConvCmp (ConvXS' zftk) ConvRX) zftk t

astConvDownSFromX :: forall sh sh' s x. (KnownSpan s, Rank sh ~ Rank sh')
                  => ShS sh -> AstTensor AstMethodLet s (TKX2 sh' x)
                  -> AstTensor AstMethodLet s (TKS2 sh x)
astConvDownSFromX sh t = case ftkAst t of
  FTKX _ x ->
    let zftk = FTKS sh x
    in astConvertDownSFromX (ConvXS' zftk) zftk t

-- The smart constructor with the prime suffix create canonical conversions
-- instead of taking a conversion as an argument.
astConvUp :: forall y z s. KnownSpan s
          => FullShapeTK z -> AstTensor AstMethodLet s y
          -> AstTensor AstMethodLet s z
astConvUp zftk t = astConvertUp (convUp (ftkAst t) zftk) zftk t

-- These three are much faster than going through convDown.
astConvUpSFromK :: forall r s. (GoodScalar r, KnownSpan s)
                => AstTensor AstMethodLet s (TKScalar r)
                -> AstTensor AstMethodLet s (TKS '[] r)
astConvUpSFromK a =
  let c2 = ConvCmp ConvXS (Conv0X STKScalar)
  in astConvertUp c2 (FTKS ZSS FTKScalar) a

-- Or should we take SNat (Rank sh) to help proving n ~ Rank sh?
astConvUpRFromS :: forall sh x s. KnownSpan s
                => IShR (Rank sh) -> AstTensor AstMethodLet s (TKS2 sh x)
                -> AstTensor AstMethodLet s (TKR2 (Rank sh) x)
astConvUpRFromS sh' t | FTKS _ x <- ftkAst t =
  let zftk = FTKR sh' x
  in astConvertUp (convUp (ftkAst t) zftk) zftk t

astConvUpXFromS :: forall sh sh' x s. (KnownSpan s, Rank sh ~ Rank sh')
                => IShX sh' -> AstTensor AstMethodLet s (TKS2 sh x)
                -> AstTensor AstMethodLet s (TKX2 sh' x)
astConvUpXFromS sh' t | FTKS _ x <- ftkAst t =
  let zftk = FTKX sh' x
  in astConvertUp (convUp (ftkAst t) zftk) zftk t

-- TODO: how to add more without duplicating astIndexKnobsS?
astIndex0
  :: forall shm s r. GoodScalar r
  => AstTensor AstMethodLet s (TKS shm r) -> AstIxS AstMethodLet shm
  -> AstTensor AstMethodLet s (TKScalar r)
astIndex0 = Ast.AstIndex0

astSum0 :: (NumScalar r, KnownSpan s)
         => AstTensor AstMethodLet s (TKS sh r)
         -> AstTensor AstMethodLet s (TKScalar r)
astSum0 t = case t of
  Ast.AstSum SNat _ u -> astSum0 u
  Ast.AstReplicate snat (STKS _ STKScalar) u ->
    astSum0 u * (fromPlain $ AstConcreteK $ fromIntegral $ fromSNat' snat)
  Ast.AstReplicate snat STKScalar u ->
    u * (fromPlain $ AstConcreteK $ fromIntegral $ fromSNat' snat)
  _ | FTKS (snat :$$ _) _ <- ftkAst t
    , Just u <- unRepl1 t ->
      astSum0 u * (fromPlain $ AstConcreteK $ fromIntegral $ fromSNat' snat)
  Ast.AstLet var u v -> astLet var u (astSum0 v)
  Ast.AstFromPrimal u -> fromPrimal $ astSum0 u
  Ast.AstFromDual u -> fromDual $ astSum0 u
  Ast.AstFromPlain u -> fromPlain $ astSum0 u
  AstTimesS t1 t2 -> astDot0 t1 t2
  Ast.AstN1S NegateOp u -> negate $ astSum0 u
  AstConcreteS v ->
    withKnownShS (Nested.sshape v) $
    astConcreteK $ tssum0 (Concrete v)
  Ast.AstAppendS u v -> astSum0 u + astSum0 v
  Ast.AstReverseS u -> astSum0 u
  Ast.AstTransposeS _ u -> astSum0 u
  Ast.AstReshapeS _ u -> astSum0 u
  Ast.AstDot1InS _ _ t1 t2 -> astDot0 t1 t2
  Ast.AstMatmul2S m@SNat SNat p@SNat m1 m2 ->
    astDot0 (astTransposeS (Permutation.makePerm @'[1, 0])
                            (astReplicate p knownSTK m1))
             (astTransposeS (Permutation.makePerm @'[0, 2, 1])
                            (astReplicate m knownSTK m2))
  _ -> case ftkAst t of
    FTKS ZSS FTKScalar -> astConvDownKFromS t
    FTKS (SNat' @1 :$$ ZSS) FTKScalar -> astIndex0 t (0 :.$ ZIS)
    _ -> Ast.AstSum0 t

astDot0 :: (NumScalar r, KnownSpan s)
         => AstTensor AstMethodLet s (TKS sh r)
         -> AstTensor AstMethodLet s (TKS sh r)
         -> AstTensor AstMethodLet s (TKScalar r)
astDot0 t1 t2 = case (t1, t2) of
  (Ast.AstSum snat1 _ u1, Ast.AstSum snat2 _ u2)
    | Just Refl <- testEquality snat1 snat2 ->
      astDot0 u1 u2
  _ | Just u1 <- unRepl t1 ->
      astConvDownKFromS u1 * astSum0 t2
  _ | Just u2 <- unRepl t2 ->
      astConvDownKFromS u2 * astSum0 t1
  ( Ast.AstReplicate snat1 (STKS _ STKScalar) u1
   ,Ast.AstReplicate snat2 (STKS _ STKScalar) u2 )
    | Just Refl <- testEquality snat1 snat2 ->
      astDot0 u1 u2
      * (fromPlain $ AstConcreteK $ fromIntegral $ fromSNat' snat1)
  ( Ast.AstReplicate snat1 STKScalar u1
   , Ast.AstReplicate snat2 STKScalar u2 )
    | Just Refl <- testEquality snat1 snat2 ->
      u1 * u2 * (fromPlain $ AstConcreteK $ fromIntegral $ fromSNat' snat1)
  _ | FTKS (snat :$$ _) _ <- ftkAst t1
    , Just u1 <- unRepl1 t1
    , Just u2 <- unRepl1 t2 ->
      astDot0 u1 u2
      * (fromPlain $ AstConcreteK $ fromIntegral $ fromSNat' snat)
  (Ast.AstFromPrimal u1, Ast.AstFromPrimal u2) ->
    fromPrimal $ astDot0 u1 u2
  (Ast.AstFromDual u1, Ast.AstFromDual u2) ->
    fromDual $ astDot0 u1 u2
  (Ast.AstFromPlain u1, Ast.AstFromPlain u2) ->
    fromPlain $ astDot0 u1 u2
  (Ast.AstN1S NegateOp u1, Ast.AstN1S NegateOp u2) -> astDot0 u1 u2
  (AstConcreteS v1, AstConcreteS v2) ->
    withKnownShS (Nested.sshape v1) $
    astConcreteK $ tsdot0 (Concrete v1) (Concrete v2)
  {- KnownNat would be needed (or SNat):
  (Ast.AstAppendS @m1 u1 v1, Ast.AstAppendS @m2 u2 v2)
    | Just Refl <- sameNat (SNat @m1) (SNat @m2) ->
      astDot0 u1 u2 + astDot0 v1 v2 -}
  (Ast.AstReverseS u1, Ast.AstReverseS u2) -> astDot0 u1 u2
  (Ast.AstTransposeS @_ @sh1 perm1 u1, Ast.AstTransposeS @_ @sh2 perm2 u2)
    | Just Refl <- testEquality perm1 perm2 ->
      gcastWith (unsafeCoerceRefl :: sh1 :~: sh2) $
      astDot0 u1 u2
  _ -> case ftkAst t1 of
    FTKS ZSS FTKScalar -> astConvDownKFromS t1 * astConvDownKFromS t2
    FTKS (SNat' @1 :$$ ZSS) FTKScalar ->
      astIndex0 t1 (0 :.$ ZIS) * astIndex0 t2 (0 :.$ ZIS)
    _ -> Ast.AstDot0 t1 t2

astDot1InS :: forall sh n r s. (NumScalar r, KnownSpan s)
           => ShS sh -> SNat n
           -> AstTensor AstMethodLet s (TKS (sh ++ '[n]) r)
           -> AstTensor AstMethodLet s (TKS (sh ++ '[n]) r)
           -> AstTensor AstMethodLet s (TKS sh r)
astDot1InS sh n@SNat t1 t2 = case (t1, t2) of
  (Ast.AstFromPrimal u1, Ast.AstFromPrimal u2) ->
    fromPrimal $ astDot1InS sh n u1 u2
  (Ast.AstFromDual u1, Ast.AstFromDual u2) ->
    fromDual $ astDot1InS sh n u1 u2
  (Ast.AstFromPlain u1, Ast.AstFromPlain u2) ->
    fromPlain $ astDot1InS sh n u1 u2
  (Ast.AstN1S NegateOp u1, Ast.AstN1S NegateOp u2) -> astDot1InS sh n u1 u2
  (AstConcreteS v1, AstConcreteS v2) ->
    withKnownShS sh $
    astConcreteS $ tsdot1In @_ @sh (SNat @n) (Concrete v1) (Concrete v2)
  _ -> Ast.AstDot1InS sh n t1 t2

astMatmul2S :: (NumScalar r, KnownSpan s)
            => SNat m -> SNat n -> SNat p
            -> AstTensor AstMethodLet s (TKS '[m, n] r)
            -> AstTensor AstMethodLet s (TKS '[n, p] r)
            -> AstTensor AstMethodLet s (TKS '[m, p] r)
astMatmul2S m@SNat n@SNat p@SNat t1 t2 = case (t1, t2) of
  (Ast.AstFromPrimal u1, Ast.AstFromPrimal u2) ->
    fromPrimal $ astMatmul2S m n p u1 u2
  (Ast.AstFromDual u1, Ast.AstFromDual u2) ->
    fromDual $ astMatmul2S m n p u1 u2
  (Ast.AstFromPlain u1, Ast.AstFromPlain u2) ->
    fromPlain $ astMatmul2S m n p u1 u2
  (AstConcreteS v1, AstConcreteS v2) ->
    astConcreteS $ tsmatmul2 (Concrete v1) (Concrete v2)
  _ -> Ast.AstMatmul2S m n p t1 t2


-- * ConvertTensor instances needed for unwinding in astConcrete

instance KnownSpan s => ConvertTensor (AstTensor AstMethodLet s) where
  tconvert c _astk v = astConvert c v

  rfromX a = case ftkAst a of
    FTKX sh' _ ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        rfromS $ sfromX @_ @sh a
  xfromR a = case ftkAst a of
    FTKR shr _ ->
      withShsFromShR shr $ \(sh :: ShS sh) ->
        withKnownShS sh $
        xfromS @_ @sh $ sfromR a

  sfromR = astConvDownSFromR knownShS
  sfromX = astConvDownSFromX knownShS
  xfromS t = case ftkAst t of
    FTKS sh x ->
      let zftk = FTKX (shCastSX knownShX sh) x
      in astConvertUp (convUp (ftkAst t) zftk) zftk t

  rzip @_ @_ @n a
   | Refl <- lemRankReplicate (Proxy @n) = case ftkAst a of
    FTKProduct (FTKR _sh y) (FTKR _ z) ->
      let c = convCmp
                (ConvXR (ftkToSTK (FTKProduct y z)))
                (convCmp
                   (ConvZip (ftkToSTK y) (ftkToSTK z))
                   (ConvT2 ConvRX ConvRX))
      in astConvert c a
  runzip @_ @_ @n a
   | Refl <- lemRankReplicate (Proxy @n) = case ftkAst a of
    FTKR _sh (FTKProduct y z) ->
      let c = convCmp
                (ConvT2 (ConvXR (ftkToSTK y)) (ConvXR (ftkToSTK z)))
                (convCmp
                   (ConvUnzip (ftkToSTK y) (ftkToSTK z))
                   ConvRX)
      in astConvert c a
  szip a = case ftkAst a of
    FTKProduct (FTKS _sh y) (FTKS _ z) ->
      let c = convCmp
                ConvXS
                (convCmp
                   (ConvZip (ftkToSTK y) (ftkToSTK z))
                   (ConvT2 ConvSX ConvSX))
      in astConvert c a
  sunzip a = case ftkAst a of
    FTKS _sh (FTKProduct y z) ->
      let c = convCmp
                (ConvT2 ConvXS ConvXS)
                (convCmp
                   (ConvUnzip (ftkToSTK y) (ftkToSTK z))
                   ConvSX)
      in astConvert c a
  xzip a = case ftkAst a of
    FTKProduct (FTKX _sh y) (FTKX _ z) ->
      let c = ConvZip (ftkToSTK y) (ftkToSTK z)
      in astConvert c a
  xunzip a = case ftkAst a of
    FTKX _sh (FTKProduct y z) ->
      let c = ConvUnzip (ftkToSTK y) (ftkToSTK z)
      in astConvert c a

  xnestR @sh1 @m @x sh1 a
    | Refl <- lemRankReplicate (Proxy @m) =
      let c :: TKConversion (TKX2 (sh1 ++ Replicate m Nothing) x)
                            (TKX2 sh1 (TKR2 m x))
          c = convCmp
                (ConvXX (ConvXR (knownSTK @x)))
                (ConvNest @_ @_ @(Replicate m Nothing)
                          (STKX sh1 (knownSTK @x)))
      in astConvert c a
  xnestS @_ @_ @x sh1 a =
    let c = convCmp (ConvXX ConvXS)
                    (ConvNest (STKX sh1 (knownSTK @x)))
    in astConvert c a
  xnest @_ @_ @x sh1 a =
    let c = ConvNest (STKX sh1 (knownSTK @x))
    in astConvert c a
  xunNestR a =
    let c = convCmp ConvUnnest
                    (ConvXX ConvRX)
    in astConvert c a
  xunNestS a =
    let c = convCmp ConvUnnest
                    (ConvXX ConvSX)
    in astConvert c a
  xunNest a =
    let c = ConvUnnest
    in astConvert c a

  tpairConv = astPair
  tunpairConv t = (astProject1 t, astProject2 t)


-- * Helper combinators

-- All but the last case are shortcuts for common forms.
astConcrete :: FullShapeTK y -> Concrete y -> AstTensor AstMethodLet PlainSpan y
{-# INLINE astConcrete #-}
astConcrete ftk v = case ftk of
  FTKScalar -> astConcreteK v
  FTKR ZSR FTKScalar ->
    Ast.AstConvert (ConvCmp (ConvXR STKScalar) (Conv0X STKScalar))
    $ AstConcreteK $ Nested.runScalar $ unConcrete v
  FTKR sh' FTKScalar ->
    withShsFromShR sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      astConvUpRFromS sh' $ astConcreteS (sfromR @_ @sh v)
  FTKS ZSS FTKScalar ->
    Ast.AstConvert (ConvCmp ConvXS (Conv0X STKScalar))
    $ AstConcreteK $ Nested.sunScalar $ unConcrete v
  FTKS _ FTKScalar -> astConcreteS v
  FTKX ZSX FTKScalar ->
    Ast.AstConvert (Conv0X STKScalar)
    $ AstConcreteK $ Nested.munScalar $ unConcrete v
  FTKX sh' FTKScalar ->
    withShsFromShX sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      astConvUpXFromS sh' $ astConcreteS (sfromX @_ @sh v)
  FTKProduct ftk1 ftk2 ->
    astPair (astConcrete ftk1 (tproject1 v)) (astConcrete ftk2 (tproject2 v))
  _ -> concreteTarget astConcreteK astConcreteS astConvUpRFromS astConvUpXFromS
                      (ftkToSTK ftk) v

-- INLINE here would bloat the binary a lot, probably negating any
-- gains from directly calling the function. Also, this is not a bottleneck.
-- It would also trigger specialization of many other functions from this
-- module, which would fail, because their unfolding is not exposed.
-- To some extend, this is even happening with no pragma (wrappers and
-- similar functions derived from this one fail to specialize in other modules).
astLetFun :: forall y z s s2. (KnownSpan s, KnownSpan s2)
          => AstTensor AstMethodLet s y
          -> (AstTensor AstMethodLet s y -> AstTensor AstMethodLet s2 z)
          -> AstTensor AstMethodLet s2 z
{-# NOINLINE astLetFun #-}
astLetFun a f | astIsSmall True a = f a
astLetFun a f = case a of
  AstConvUp @y2 ftkz v ->
    unsafePerformIO $ do
      var <- funToAstNoBoundsIO (ftkAst v)
      pure $! astLet var v (f $ astConvUp @y2 ftkz $ astVar var)
  Ast.AstFromPrimal v -> astLetFun v (f . fromPrimal)
  Ast.AstFromDual v -> astLetFun v (f . fromDual)
  Ast.AstFromPlain v -> astLetFun v (f . fromPlain)
  _ -> unsafePerformIO $ case ftkAst a of
    ftk@FTKScalar -> do
        var <- funToAstAutoBoundsIO ftk a
        pure $! astLet var a (f $ astVar var)
    FTKR sh' x ->
      withShsFromShR sh' $ \(sh :: ShS sh) -> do
        let v = astConvDownSFromR sh a
        var <- funToAstNoBoundsIO (FTKS sh x)
        pure $! astLet var v (f $ astConvUpRFromS sh' $ astVar var)
          -- safe, because subsitution ruled out above
    FTKX sh' x ->
      withShsFromShX sh' $ \(sh :: ShS sh) -> do
        let v = astConvDownSFromX sh a
        var <- funToAstNoBoundsIO (FTKS sh x)
        pure $! astLet var v (f $ astConvUpXFromS sh' $ astVar var)
    FTKS ZSS x@FTKScalar -> do
        let v = astConvDownKFromS a
        var <- funToAstAutoBoundsIO x v
        pure $! astLet var v (f $ astConvUpSFromK $ astVar var)
    -- calling recursively for product may be not worth it
    ftk -> do
        var <- funToAstNoBoundsIO ftk
        pure $! astLet var a (f $ astVar var)

astReplicateNS :: forall shn shp s x. KnownSpan s
               => ShS shn -> AstTensor AstMethodLet s (TKS2 shp x)
               -> AstTensor AstMethodLet s (TKS2 (shn ++ shp) x)
astReplicateNS shn v | STKS shp x <- ftkToSTK (ftkAst v) =
  let go :: ShS shn' -> AstTensor AstMethodLet s (TKS2 (shn' ++ shp) x)
      go ZSS = v
      go (snat :$$ shn2) =
        astReplicate snat (STKS (shn2 `shsAppend` shp) x) $ go shn2
  in go shn

unRepl :: KnownSpan s
       => AstTensor AstMethodLet s (TKS2 sh x)
       -> Maybe (AstTensor AstMethodLet s (TKS2 '[] x))
unRepl (Ast.AstReplicate _ (STKS ZSS _) u) = Just u
unRepl (Ast.AstReplicate _ STKScalar u) = Just $ astConvUpSFromK u
unRepl (Ast.AstReplicate _ STKS{} u) = unRepl u
unRepl (AstConcreteS a) = AstConcreteS . Nested.sscalar <$> sunReplicatePrim a
unRepl (Ast.AstCond b v1 v2) = do
  u1 <- unRepl v1
  u2 <- unRepl v2
  return $! astCond b u1 u2
unRepl (Ast.AstLet var u t) = Ast.AstLet var u <$> unRepl t
unRepl (Ast.AstPrimalPart t) = astPrimalPart <$> unRepl t
unRepl (Ast.AstDualPart t) = astDualPart <$> unRepl t
unRepl (Ast.AstPlainPart t) = astPlainPart <$> unRepl t
unRepl (Ast.AstFromPrimal t) = fromPrimal <$> unRepl t
unRepl (Ast.AstFromDual t) = fromDual <$> unRepl t
unRepl (Ast.AstFromPlain t) = fromPlain <$> unRepl t
unRepl _ = Nothing

unRepl1 :: KnownSpan s
        => AstTensor AstMethodLet s (TKS2 (n ': sh) x)
        -> Maybe (AstTensor AstMethodLet s (TKS2 sh x))
unRepl1 (Ast.AstReplicate _ STKS{} u) = Just u
unRepl1 (Ast.AstReplicate _ STKScalar u) = Just $ astConvUpSFromK u
unRepl1 (AstConcreteS a) = AstConcreteS <$> sunReplicate1 a
unRepl1 (Ast.AstCond b v1 v2) = do
  u1 <- unRepl1 v1
  u2 <- unRepl1 v2
  return $! astCond b u1 u2
unRepl1 (Ast.AstLet var u t) = Ast.AstLet var u <$> unRepl1 t
unRepl1 (Ast.AstPrimalPart t) = astPrimalPart <$> unRepl1 t
unRepl1 (Ast.AstDualPart t) = astDualPart <$> unRepl1 t
unRepl1 (Ast.AstPlainPart t) = astPlainPart <$> unRepl1 t
unRepl1 (Ast.AstFromPrimal t) = fromPrimal <$> unRepl1 t
unRepl1 (Ast.AstFromDual t) = fromDual <$> unRepl1 t
unRepl1 (Ast.AstFromPlain t) = fromPlain <$> unRepl1 t
unRepl1 _ = Nothing

unReplN :: KnownSpan s
        => ShS shm -> AstTensor AstMethodLet s (TKS2 (shm ++ shn) x)
        -> Maybe (AstTensor AstMethodLet s (TKS2 shn x))
unReplN ZSS a = Just a
unReplN (_ :$$ ZSS) (Ast.AstReplicate _ STKScalar u) = Just $ astConvUpSFromK u
unReplN (_ :$$ sh) (Ast.AstReplicate _ STKS{} u) = unReplN sh u
unReplN shm (AstConcreteS a) = AstConcreteS <$> sunReplicateN shm a
unReplN shm (Ast.AstCond b v1 v2) = do
  u1 <- unReplN shm v1
  u2 <- unReplN shm v2
  return $! astCond b u1 u2
unReplN shm (Ast.AstLet var u t) = Ast.AstLet var u <$> unReplN shm t
unReplN shm (Ast.AstPrimalPart t) = astPrimalPart <$> unReplN shm t
unReplN shm (Ast.AstDualPart t) = astDualPart <$> unReplN shm t
unReplN shm (Ast.AstPlainPart t) = astPlainPart <$> unReplN shm t
unReplN shm (Ast.AstFromPrimal t) = fromPrimal <$> unReplN shm t
unReplN shm (Ast.AstFromDual t) = fromDual <$> unReplN shm t
unReplN shm (Ast.AstFromPlain t) = fromPlain <$> unReplN shm t
unReplN _ _ = Nothing


-- * Substitution wrappers

-- | We assume no variable is shared between a binding and its nested binding
-- and nobody substitutes into variables that are bound.
-- This keeps the substitution code simple, because we never need to compare
-- variables to any variable in the bindings.
substituteAst :: forall s s2 y z. KnownSpan s
              => AstTensor AstMethodLet s2 z -> AstVarName '(s2, z)
              -> AstTensor AstMethodLet s y
              -> AstTensor AstMethodLet s y
substituteAst i var v1 =
  fromMaybe v1 $ substitute1Ast i var v1

substituteAstIxS
  :: AstTensor AstMethodLet s y -> AstVarName '(s, y) -> AstIxS AstMethodLet sh
  -> AstIxS AstMethodLet sh
substituteAstIxS i var ix =
  fromMaybe ix $ substitute1AstIxS i var ix


-- * Substitution workers

-- Invariant: if the variable has bounds, the expression can only have
-- values within the bounds (regardless of what the `bounds` call would say).
substitute1Ast :: forall s s2 y z. KnownSpan s
               => AstTensor AstMethodLet s2 z -> AstVarName '(s2, z)
               -> AstTensor AstMethodLet s y
               -> Maybe (AstTensor AstMethodLet s y)
substitute1Ast i var = subst where
 substIxS :: AstIxS AstMethodLet sh3 -> Maybe (AstIxS AstMethodLet sh3)
 substIxS ix =
   let mix = fmap subst ix
   in if any isJust mix
      then Just $ ixsZipWith fromMaybe ix mix
      else Nothing
 subst :: forall s3 y2. KnownSpan s3
       => AstTensor AstMethodLet s3 y2 -> Maybe (AstTensor AstMethodLet s3 y2)
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
    -- We can't assert anything here about bounds, because only runtime concrete
    -- concrete values need to be in bounds and bounds approximations
    -- don't have to agree.
    if varNameToAstVarId var == varNameToAstVarId var2
    then case testEquality var var2 of
      Just Refl -> case (i, var2) of
        (Ast.AstVar var3, AstVarName _ (FtkAndBoundsBounds lb2 ub2)) ->
          let bs = case var3 of
                AstVarName _ (FtkAndBoundsBounds lb3 ub3) ->
                  (max lb2 lb3, min ub2 ub3)
                    -- We know all bounds approximations have to be correct
                    -- so we can intersect them. We ignore approximations
                    -- from @var, because they should be equal to those of var2,
                    -- because we never shadow variables nor update their types.
                _ -> (lb2, ub2)
          in Just $ astVar $ reboundsVarName bs var3
        _ -> Just i
      _ -> error $ "substitute1Ast: kind of the variable "
                   ++ show var2 ++ ": " ++ show (varNameToFTK var)
                   ++ ", payload kind: " ++ show (varNameToFTK var2)
                   ++ ", payload: " ++ show i
    else Nothing
  Ast.AstCond b v w ->
    case (subst b, subst v, subst w) of
      (Nothing, Nothing, Nothing) -> Nothing
      (mb, mv, mw) ->
        Just $ astCond (fromMaybe b mb) (fromMaybe v mv) (fromMaybe w mw)
  Ast.AstBuild1 k stk (var2, v) ->
    assert (varNameToAstVarId var2 /= varNameToAstVarId var) $
    case subst v of
      Just !v2 -> Just $ Ast.AstBuild1 k stk (var2, v2)
      Nothing -> Nothing

  Ast.AstLet var2 u v ->
    case (withKnownSpan (varNameToSpan var2) $ subst u, subst v) of
      (Nothing, Nothing) -> Nothing
      (mu, mv) -> Just $ astLet var2 (fromMaybe u mu) (fromMaybe v mv)

  Ast.AstPrimalPart a -> astPrimalPart <$> subst a
  Ast.AstDualPart a -> astDualPart <$> subst a
  Ast.AstPlainPart a -> astPlainPart <$> subst a
  Ast.AstFromPrimal a -> fromPrimal <$> subst a
  Ast.AstFromDual a -> fromDual <$> subst a
  Ast.AstFromPlain a -> fromPlain <$> subst a

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
  Ast.AstArgMinK v -> astArgMinK <$> subst v
  Ast.AstArgMaxK v -> astArgMaxK <$> subst v

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
  Ast.AstArgMinS a -> Ast.AstArgMinS <$> subst a
  Ast.AstArgMaxS a -> Ast.AstArgMaxS <$> subst a

  Ast.AstIndexS shn v ix ->
    case (subst v, substIxS ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astIndexS shn (fromMaybe v mv) (fromMaybe ix mix)
  Ast.AstScatterS shm shn shp v (vars, ix) ->
    case (subst v, substIxS ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astScatterS shm shn shp
                                      (fromMaybe v mv)
                                      (vars, fromMaybe ix mix)
  Ast.AstGatherS shm shn shp v (vars, ix) ->
    case (subst v, substIxS ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astGatherS shm shn shp
                                     (fromMaybe v mv)
                                     (vars, fromMaybe ix mix)
  Ast.AstIotaS{} -> Nothing
  Ast.AstAppendS x y ->
    case (subst x, subst y) of
      (Nothing, Nothing) -> Nothing
      (mx, my) -> Just $ astAppendS (fromMaybe x mx) (fromMaybe y my)
  Ast.AstSliceS i2 n k v -> astSliceS i2 n k <$> subst v
  Ast.AstReverseS v -> astReverseS <$> subst v
  Ast.AstTransposeS perm v -> astTransposeS perm <$> subst v
  Ast.AstReshapeS sh v -> astReshapeS sh <$> subst v

  Ast.AstConvert c v -> astConvert c <$> subst v

  Ast.AstIndex0 v ix ->
    case (subst v, substIxS ix) of
      (Nothing, Nothing) -> Nothing
      (mv, mix) -> Just $ astIndex0 (fromMaybe v mv) (fromMaybe ix mix)
  Ast.AstSum0 v -> astSum0 <$> subst v
  Ast.AstDot0 u v ->
    let mu = subst u
        mv = subst v
    in if isJust mu || isJust mv
       then Just $ astDot0 (fromMaybe u mu) (fromMaybe v mv)
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
  Ast.AstBoolNotK arg -> notB <$> subst arg
  Ast.AstBoolNotS arg -> Ast.AstBoolNotS <$> subst arg
  Ast.AstBoolAndK arg1 arg2 ->
    let mb1 = subst arg1
        mb2 = subst arg2
    in if isJust mb1 || isJust mb2
       then Just $ fromMaybe arg1 mb1 &&* fromMaybe arg2 mb2
       else Nothing
  Ast.AstBoolAndS arg1 arg2 ->
    let mb1 = subst arg1
        mb2 = subst arg2
    in if isJust mb1 || isJust mb2
       then Just $ fromMaybe arg1 mb1 `Ast.AstBoolAndS` fromMaybe arg2 mb2
       else Nothing
  Ast.AstLeqK arg1 arg2 ->
    let mr1 = subst arg1
        mr2 = subst arg2
    in if isJust mr1 || isJust mr2
       then Just $ fromMaybe arg1 mr1 <=. fromMaybe arg2 mr2
       else Nothing
  Ast.AstLeq arg1 arg2 ->
    let mr1 = subst arg1
        mr2 = subst arg2
    in if isJust mr1 || isJust mr2
       then Just $ fromMaybe arg1 mr1 <=. fromMaybe arg2 mr2
       else Nothing
  Ast.AstLeqS shb sh arg1 arg2 ->
    let mr1 = subst arg1
        mr2 = subst arg2
    in if isJust mr1 || isJust mr2
       then Just $ Ast.AstLeqS shb sh (fromMaybe arg1 mr1) (fromMaybe arg2 mr2)
       else Nothing

substitute1AstIxS
  :: AstTensor AstMethodLet s2 y -> AstVarName '(s2, y) -> AstIxS AstMethodLet sh
  -> Maybe (AstIxS AstMethodLet sh)
substitute1AstIxS i var ix =
  let mix = fmap (substitute1Ast i var) ix
  in if any isJust mix
     then Just $ ixsZipWith fromMaybe ix mix
     else Nothing

substitute1AstHFun
  :: forall s s3 x y z.
     AstTensor AstMethodLet s3 z -> AstVarName '(s3, z) -> AstHFun s x y
  -> Maybe (AstHFun s x y)
substitute1AstHFun _i _var AstLambda{} =
  Nothing  -- no outside free variables
