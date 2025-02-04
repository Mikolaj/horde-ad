{-# LANGUAGE AllowAmbiguousTypes, DerivingStrategies, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | TODO: This and most of other haddocks in this module are out of date.
--
-- The second component of our rendition of dual numbers:
-- delta expressions, with their semantics.
--
-- A delta expression can be viewed as a concise representation
-- of a linear map (which is the derivative of the objective function)
-- and its evaluation on a given argument as an adjoint (in the algebraic
-- sense) of the linear map applied to that argument. Since linear maps
-- can be represented as matrices, this operation corresponds
-- to a transposition of the matrix. However, the matrix is not constructed,
-- but is represented and transposed preserving the sparsity
-- of the representation.
--
-- The \'sparsity\' is less obvious when the domain of the function consists
-- of multiple vectors, matrices and tensors and when the expressions themselves
-- contain vectors, matrices and tensors. However, a single tiny delta
-- expression (e.g., a sum of two inputs) may denote a vector of matrices.
-- Even a delta expression containing a big matrix usually denotes something
-- much bigger: a whole vector of such matrices and more.
--
-- The algebraic structure here is an extension of vector space.
-- The crucial extra constructor of an input replaces the one-hot
-- access to parameters with something cheaper and more uniform.
-- A lot of the remaining additional structure is for introducing
-- and reducing dimensions (ranks).
--
-- This simplified rendering of the library now contains two ranks:
-- scalars and (ranked) tensors. However, most haddocks and code comments
-- are unchanged since the times vectors were available instead of tensors.
-- The newer setting is a straightforward generalization of the older one,
-- so the rewritten comments would be very similar and slightly harder
-- to understand.
module HordeAd.Core.DeltaEval
  ( -- * Delta expression evaluation
    gradientFromDelta, derivativeFromDelta
    -- * Exported to be specialized elsewhere
  , evalRevFromnMap, EvalState
  ) where

import Prelude

import Control.Arrow (second)
import Control.Exception.Assert.Sugar
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Some
import Data.Traversable (mapAccumL)
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, type (+))
import Text.Show (showListWith)
import Text.Show.Functions ()
import Type.Reflection (typeRep)

import Data.Array.Mixed.Permutation (permInverse)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (shxTakeSSX, ssxFromShape, withKnownShX)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested
  (KnownShS (..), KnownShX (..), Rank, ShR (..), ShS (..), ShX (..))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape
  (shrRank, shsPermutePrefix, shsProduct, shsRank, withKnownShS)

import HordeAd.Core.Delta
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

-- * Computing derivatives from delta expressions

gradientFromDelta
  :: forall x z target.
     (ADReadyNoLet target, ShareTensor target, KnownSTK z)
  => FullTensorKind x
  -> FullTensorKind z
  -> Maybe (target (ADTensorKind z))
  -> Delta target z
  -> target (ADTensorKind x)
gradientFromDelta !parameters0 zftk !mdt deltaTopLevel =
  let oneAtF = constantTarget 1 $ adFTK zftk
      dt = fromMaybe oneAtF mdt
      s0 = initEvalState parameters0
      s1 = evalRev s0 dt deltaTopLevel
      s2 = evalRevFromnMap s1
      (res, remainder) =
        rebuildInputs @(ADTensorKind x) (DMap.elems $ iMap s2) s2
        $ adFTK parameters0
  in assert (null remainder) res

showsPrec_iMap
  :: (forall y. KnownSTK y => Show (TensorOrZero target y))
  => Int -> IMap target -> ShowS
showsPrec_iMap d demap =
  showParen (d > 10) $
    showString "fromList "
    . showListWith
        (\(k :=> target) ->
          case tensorKindFromInputId k of
            Dict -> showsPrec 2 k . showString " :=> " . showsPrec 1 target)
        (DMap.toList demap)

show_iMap
  :: (forall y. KnownSTK y => Show (TensorOrZero target y))
  => IMap target -> String
show_iMap iMap = showsPrec_iMap 0 iMap ""

derivativeFromDelta
  :: forall x z target.
     ( ADReadyNoLet target, ShareTensor target, KnownSTK x, KnownSTK z )
  => Delta target z -> target (ADTensorKind x)
  -> target (ADTensorKind z)
derivativeFromDelta deltaTopLevel ds
  | Dict <- lemKnownSTKOfAD (knownSTK @x) =
    let iMap = DMap.fromDistinctAscList $ fst
               $ generateDSums 0 (tftk knownSTK ds) ds
        s0 = DMap.empty
        !(!_s2, !c) = evalFwd iMap s0 deltaTopLevel
    in c


-- * Auxiliary datatypes for Delta evaluation

type ADMap target = DEnumMap (NodeId target) (Cotangent target)

type IMap target = DEnumMap (InputId target) (TensorOrZero target)

type role Cotangent nominal nominal
newtype Cotangent target y =
  Cotangent {unCotangent :: target (ADTensorKind y)}

-- This is a tensor representation where, as much as feasible,
-- zero tensors are marked specially in order to be cheap to detect
-- (as opposed to require traversing large terms or checking that
-- each cell of a huge array is zero or both).
-- It also makes (an insignificant) case of addTensorOrZero cheaper.
type role TensorOrZero nominal nominal
data TensorOrZero target y =
    Tensor (STensorKind y) (target y)
  | Zero (FullTensorKind y)
  deriving Show

evalTensorOrZero :: forall target x. ADReadyNoLet target
                 => TensorOrZero target x -> target x
evalTensorOrZero = \case
  Tensor _ t -> t
  Zero ftk -> constantTarget 0 ftk

addTensorOrZero :: forall target y. ADReadyNoLet target
                => TensorOrZero target y -> TensorOrZero target y
                -> TensorOrZero target y
addTensorOrZero a b = case (a, b) of
  (Tensor stk ta, Tensor _ tb) -> Tensor stk $ addTarget stk ta tb
    -- target has a ShareTensor instance, so ta and tb don't need
    -- to be duplicable
  (Zero{}, _) -> b
  (_, Zero{}) -> a

-- Matches generateDSumsDummy.
rebuildInputs :: forall ady target. ADReadyNoLet target
              => [Some (TensorOrZero target)]
              -> EvalState target  -- original state; only for error messages
              -> FullTensorKind ady
              -> (target ady, [Some (TensorOrZero target)])
rebuildInputs els s2 ftk = case ftk of
  FTKProduct @y1 @y2 ftk1 ftk2
   | Dict <- lemKnownSTK (ftkToSTK ftk1)
   , Dict <- lemKnownSTK (ftkToSTK ftk2) ->
      let (t1, rest1) = rebuildInputs @y1 els s2 ftk1
          (t2, rest2) = rebuildInputs @y2 rest1 s2 ftk2
      in (tpair t1 t2, rest2)
  _ -> case els of
    Some tz@(Tensor stk t) : rest ->
      case sameSTK stk (ftkToSTK ftk) of
        Just Refl -> (t, rest)
        _ | Dict <- lemKnownSTK stk ->
          error $ "rebuildInputs: wrong Tensor type: "
                  ++ show (tz, show_iMap (iMap s2))
    Some tz@(Zero ftk2) : rest ->
      case sameSTK (ftkToSTK ftk2) (ftkToSTK ftk) of
        Just Refl -> (constantTarget 0 ftk, rest)
          -- TODO: actually pass this ZERO through to optimizers
          -- and use there to avoid updating the gradient
          -- and maybe use elsewhere, too.
        _ | Dict <- lemKnownSTK (ftkToSTK ftk2) ->
          error $ "rebuildInputs: wrong Zero type: "
                  ++ show (tz, show_iMap (iMap s2))
    _ -> error $ "rebuildInputs: illegal TensorOrZero: "
                 ++ show_iMap (iMap s2)

-- Matches generateDeltaInputs.
generateDSumsDummy :: Int -> FullTensorKind y
                   -> ([DSum (InputId target) (TensorOrZero target)], Int)
generateDSumsDummy j ftk  = case ftk of
  FTKProduct ftk1 ftk2 ->
    let (ds1, j1) = generateDSumsDummy j ftk1
        (ds2, j2) = generateDSumsDummy j1 ftk2
    in (ds1 ++ ds2, j2)
  _ | Dict <- lemKnownSTK (ftkToSTK ftk) ->
    ([InputId j :=> Zero ftk], j + 1)

-- Matches generateDeltaInputs.
generateDSums :: ShareTensor target
              => Int -> FullTensorKind y -> target y
              -> ([DSum (InputId target) (TensorOrZero target)], Int)
generateDSums j ftk t = case ftk of
  FTKProduct ftk1 ftk2 | Dict <- lemKnownSTK (ftkToSTK ftk1)
                       , Dict <- lemKnownSTK (ftkToSTK ftk2) ->
    let (t1, t2) = tunpair t
        (ds1, j1) = generateDSums j ftk1 t1
        (ds2, j2) = generateDSums j1 ftk2 t2
    in (ds1 ++ ds2, j2)
  _ | Dict <- lemKnownSTK (ftkToSTK ftk) ->
    ([InputId j :=> Tensor (ftkToSTK ftk) t], j + 1)

-- * Delta evaluation state

-- | The state of evaluation. It consists of several maps.
-- The maps indexed by input identifiers and node identifiers
-- eventually store cotangents for their respective nodes.
-- The cotangents are built gradually during the evaluation,
-- by summing cotangent contributions.
--
-- Data invariant:
-- 1. keys nMap == keys dMap
-- 2. key `member` dMap == nMap!key is ...
type role EvalState nominal
data EvalState target = EvalState
  { iMap :: IMap target
      -- ^ eventually, cotangents of objective function inputs
      -- (eventually copied to the vector representing the gradient
      -- of the objective function);
      -- the identifiers need to be contiguous and start at 0
  , dMap :: ADMap target
      -- ^ eventually, cotangents of non-input subterms indexed
      -- by their node identifiers
  , nMap :: DEnumMap (NodeId target) (Delta target)
      -- ^ nodes left to be evaluated;
      -- we can't evaluate them at once, because their other shared copies
      -- may still not be processed, so we'd not take advantage of the sharing
      -- and not take into account the whole summed context when finally
      -- evaluating
  }

-- | Delta expressions naturally denote forward derivatives, as encoded
-- in function 'derivativeFromDelta'. However, we are usually more
-- interested in computing gradients, which is what @gradientFromDelta@ does.
-- The two functions are bound by the equation from Lemma 5 from the paper
-- "Provably correct, asymptotically efficient, higher-order reverse-mode
-- automatic differentiation":
--
-- > dt <.> derivativeFromDelta d ds = gradientFromDelta d dt <.> ds
--
-- where @\<.\>@ denotes generalized dot product (multiplying
-- all tensors element-wise and summing the results), @d@ is the top level
-- delta expression from translation of the objective function @f@ to dual
-- numbers, @ds@ belongs to the domain of @f@ and @dt@ to the codomain.
-- In other words, @ds@ is a perturbation (small change) of the arguments
-- of @f@, for which we compute the derivative, and @dt@ is a perturbation
-- of the result of @f@, for which we compute the gradient.
-- We omitted for clarity the @dim@ arguments that are
-- the lengths of vectors of the tensors in the domain of @f@.
--
-- Let's first discuss in detail the semantics of delta-expressions
-- in terms of forward derivatives, since it's more straightforward.
-- Let @r@ be the type of underlying scalars. Let @f@ be a mathematical
-- differentiable function that takes arguments (a collection
-- of finite maps or vectors) of type @HVector r@ and produces
-- a single result of type @r@. Let a dual number counterpart
-- of @f@ applied to a fixed collection of parameters @P@
-- of type @HVector r@ be represented as a Haskell value @b@.
-- Let @d :: Delta0 r@ be the delta expression that is
-- the second component of @b@, let @ds@ belong to @HVector r@.
-- The semantics of @d@ is a linear function from @HVector r@
-- to @r@ that is the derivative of @f@ at point @P@
-- with respect to the perturbation @ds@. The mathematical formula
-- for the derivative follows straightforwardly the syntactic form
-- of the delta expression @d@ (see 'derivativeFromDelta').
--
-- Let's now describe the semantics of a delta expression @d@
-- as the gradient of @f@ at point @P@ with respect to a @dt@ that belongs
-- to @r@. Here the semantics of @d@ is a collection of finite maps
-- (vectors) @v0@, @v1@, ..., corresponding to @HVector r@.
-- The value of @vi@ at index @k@ is the partial derivative
-- of function @f@ at @P@ with respect to its parameter of type @ai@
-- residing at index @k@.
--
-- Consequently, obtaining the gradient amounts to transposing the linear map
-- that is straightforwardly represented by a delta expression. The @eval@
-- functions in @buildFinMaps@ below transpose a linear map and,
-- at the same time, evalute the transposed map, producing its value
-- when applied to afixed argument (contained in the second
-- parameter of @buildFinMaps@).
--
-- Function @gradientFromDelta@ computes the four vectors described above.
-- Requested lengths of the vectors are given in the first few arguments.
-- The delta expression to be evaluated, together with the @dt@ perturbation
-- value (usually set to @1@) are given as arguments.
initEvalState
  :: FullTensorKind x -> EvalState target
initEvalState ftk0 =
  let -- Create finite maps that hold values associated with inputs
      -- and with (possibly shared) term tree nodes.
      -- The former are usually initialized with dummy values so that it's cheap
      -- to check if any update has already been performed to a cell
      -- (allocating big vectors filled with zeros is too costly,
      -- especially if never used in an iteration, and adding to such vectors
      -- and especially using them as cotangent accumulators is wasteful.
      -- We take care to keep the scalar type of the dummy correct,
      -- but a shape is not preserved in a dummy, so it's not shape-correct.
      iMap = DMap.fromDistinctAscList
             $ fst $ generateDSumsDummy 0 $ adFTK ftk0
      dMap = DMap.empty
      nMap = DMap.empty
  in EvalState {..}


-- * Reverse pass, transpose/evaluation of the delta expressions

-- The first argument is the evaluation state being modified,
-- the second is the cotangent accumulator that will become an actual
-- cotangent contribution when complete (see below for an explanation)
-- and the third argument is the node to evaluate.
evalRevRuntimeSpecialized
  :: forall n r target.
     (GoodScalar r, KnownNat n, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind (TKR n r))
  -> Delta target (TKR n r)
  -> EvalState target
evalRevRuntimeSpecialized !s !c =
  -- We dispatch on all expected underyling scalar types, which is
  -- necessary to run the correct specialization when unpacking
  -- an existential type. All IfDifferentiable and RowSum instances should
  -- be included in the list of expected underlying scalar types.
  -- If the scalar type is not on the list, performance suffers greatly.
  -- TODO: can I pattern match on (typeRep @r) instead?
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalRevSame @(TKR n Double) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalRevSame @(TKR n Float) s c
      _ -> const s

evalSRuntimeSpecialized
  :: forall sh r target.
     (GoodScalar r, KnownShS sh, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind (TKS sh r))
  -> Delta target (TKS sh r)
  -> EvalState target
evalSRuntimeSpecialized !s !c =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalRevSame @(TKS sh Double) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalRevSame @(TKS sh Float) s c
      _ -> const s

evalXRuntimeSpecialized
  :: forall sh r target.
     (GoodScalar r, KnownShX sh, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind (TKX sh r))
  -> Delta target (TKX sh r)
  -> EvalState target
evalXRuntimeSpecialized !s !c =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalRevSame @(TKX sh Double) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalRevSame @(TKX sh Float) s c
      _ -> const s

evalRev
  :: forall y target.
     (KnownSTK y, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalRev !s !c d0 = case d0 of
  -- All constructors that admit a TKProduct kind need to be handled in evalRev
  -- except for DeltaInput that is always constructed only in basic kinds.
  DeltaPair @y1 @y2 d1 d2 | Dict <- lemKnownSTKOfAD (knownSTK @y1)
                      , Dict <- lemKnownSTKOfAD (knownSTK @y2) ->
    let (c1, c2) = tunpair c
    in evalRev (evalRev s c1 d1) c2 d2
  DeltaProject1 @_ @z d | Dict <- lemKnownSTKOfAD (knownSTK @y)
                    , Dict <- lemKnownSTKOfAD (knownSTK @z) ->
    case ftkDelta d of
      FTKProduct _ ftk2 ->
        let zero = constantTarget 0 $ adFTK ftk2
        in evalRev s (tpair c zero) d
    -- if y is, e.g., TKR Int 0, we eval this delta even though we could ignore it
    -- at the price of complicating or duplicating the code slightly more
  DeltaProject2 @x d | Dict <- lemKnownSTKOfAD (knownSTK @y)
                 , Dict <- lemKnownSTKOfAD (knownSTK @x) ->
    case ftkDelta d of
      FTKProduct ftk1 _ ->
        let zero = constantTarget 0 $ adFTK ftk1
        in evalRev s (tpair zero c) d
  DeltaFromVector snat stk ld | Refl <- lemBuildOfAD snat stk
                          , Dict <- lemKnownSTKOfAD (knownSTK @y) ->
    let cShared = tshare c
        cxs = tunravelToListShare snat (adSTK stk) cShared
    in foldl' (\ !s2 (cx, d2) -> evalRev s2 cx d2) s
       $ zip cxs (V.toList ld)
  DeltaSum snat stk d | Refl <- lemBuildOfAD snat stk ->
    evalRev s (treplicateShare snat (adSTK stk) c) d
  DeltaReplicate snat stk d | Refl <- lemBuildOfAD snat stk ->
    evalRev s (tsumShare snat (adSTK stk) c) d
  DeltaMapAccumR @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            _df rf acc0' es'
   | Dict <- lemKnownSTKOfAD (knownSTK @accShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @bShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @eShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @accShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @eShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @(ADTensorKind bShs))
   , Dict <- lemKnownSTKOfBuild k (knownSTK @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (knownSTK @bShs)
   , Refl <- lemBuildOfAD k (knownSTK @eShs) ->
    let accShsAD = adFTK accShs
        bShsAD = adFTK bShs
        eShsAD = adFTK eShs
        (c0, crest) = tunpair c
        dacc_des =
          tmapAccumL (Proxy @target)
                     k accShsAD eShsAD (FTKProduct bShsAD
                                                   (FTKProduct accShs eShs))
                     (\dx db_acc_e ->
                        tlet db_acc_e $ \ !db_acc_e1 ->
                          unHFun rf (tpair (tpair dx (tproject1 db_acc_e1))
                                           (tproject2 db_acc_e1)))
                     c0
                     (tpair crest (tpair q es))
        (dacc, des) = tunpair dacc_des
        s2 = evalRev s dacc acc0'
    in evalRev s2 des es'
  DeltaMapAccumL @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            _df rf acc0' es'
   | Dict <- lemKnownSTKOfAD (knownSTK @accShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @bShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @eShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @accShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @eShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @(ADTensorKind bShs))
   , Dict <- lemKnownSTKOfBuild k (knownSTK @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (knownSTK @bShs)
   , Refl <- lemBuildOfAD k (knownSTK @eShs) ->
    let accShsAD = adFTK accShs
        bShsAD = adFTK bShs
        eShsAD = adFTK eShs
        (c0, crest) = tunpair c
        dacc_des =
          tmapAccumR (Proxy @target)
                     k accShsAD eShsAD (FTKProduct bShsAD
                                                   (FTKProduct accShs eShs))
                     (\dx db_acc_e ->
                        tlet db_acc_e $ \ !db_acc_e1 ->
                          unHFun rf (tpair (tpair dx (tproject1 db_acc_e1))
                                           (tproject2 db_acc_e1)))
                     c0
                     (tpair crest (tpair q es))
        (dacc, des) = tunpair dacc_des
        s2 = evalRev s dacc acc0'
    in evalRev s2 des es'

  DeltaShare n d | Dict <- lemKnownSTKOfAD (knownSTK @y) ->
    -- In this context, by construction, @d@ is the dual component
    -- of a dual number term. Let's say that, at this point, evaluation
    -- considers position (node) p out of possibly multiple positions
    -- at which that dual number resides in the whole term tree
    -- of the dual number representation of the objective function.
    -- (Equivalently, considers edges p, one of many leading to the only
    -- node with identifier @n@ in the DAG representing the term).
    -- If so, the @c@ argument of @eval0@ is the cotangent
    -- contribution for position p, that is, the partial derivative
    -- of the objective function with respect to position p.
    --
    -- If there are indeed multiple such positions (the term is shared)
    -- then, over the course of evaluation, cotangent contributions
    -- of them all are gradually accumulated in the finite
    -- maps and eventually their total sum represents the total
    -- influence of the objective function's subcomputation
    -- (more precisely, subgraph of the data flow graph in question)
    -- corresponding to the shared term @DeltaShare n d@. This total
    -- influence over the objective function's behaviour is called
    -- in short the cotangent of the node identifier @n@.
    -- In other words, the cotangent of @n@ is the sum,
    -- over all positions (edges) q in the global delta-expression DAG
    -- that are a reference to node @n@, of the partial derivative
    -- of the objective function with respect to the subcomputation
    -- corresponding to @q@ (meaning, subcomputations denoted by
    -- Haskell terms whose dual components are @Share n ...@).
    --
    -- For @Input@ terms, the eventual lists of cotangents end up
    -- in the cells of the gradient vectors that are the final
    -- result of the evaluation.
    assert (case d of  -- shouold match shareDelta
              DeltaZero{} -> False
              DeltaPair{} -> False
              DeltaInput{} -> False
              DeltaShare{} -> False
              _ -> True)
    $ case DMap.lookup n $ nMap s of
        Just _ ->
          let addc x = Cotangent $ addTarget knownSTK c (unCotangent x)
            -- target has a ShareTensor instance, so addTarget arguments
            -- don't need to be duplicable
          in s {dMap = DMap.adjust addc n $ dMap s}
        Nothing ->
          let cd = Cotangent c
          in s { nMap = DMap.insert n d $ nMap s
               , dMap = DMap.insert n cd $ dMap s }

  DeltaFromS @_ @z (DeltaSFromR @sh @x d)
    | Just Refl <- sameSTK (adSTK (knownSTK @z))
                           (adSTK (knownSTK @(TKR2 (Rank sh) x))) ->
      evalRev s c d
  DeltaFromS @_ @z (DeltaSFromX @_ @sh' @x d)
    | Just Refl <- sameSTK (adSTK (knownSTK @z))
                           (adSTK (knownSTK @(TKX2 sh' x))) ->
      evalRev s c d
  DeltaFromS @y7 @z d -> case (knownSTK @y7, knownSTK @z) of
    (stky, stkz) | Just Refl <- sameSTK stky stkz -> evalRev s c d
    (STKS ZSS yx@(STKScalar try), STKScalar trz) ->
      case testEquality try trz of
        Just Refl -> case sameSTK yx (adSTK yx) of
          Just Refl -> evalRev s (sfromK c) d
          _ -> s
        Nothing -> error "evalRev: tensor kinds don't match"
    (STKS shy yx, STKR nx@SNat zx) | Dict <- lemKnownSTKOfAD yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) nx) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          evalRev s (sfromR c) d
        _ -> error "evalRev: tensor kinds don't match"
    (STKS shy yx, STKX shx zx) | Dict <- lemKnownSTKOfAD yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) (ssxRank shx)) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          withKnownShX shx $
          evalRev s (sfromX c) d
        _ -> error "evalRev: tensor kinds don't match"
    (STKProduct @y1 @y2 stky1 stky2, STKProduct @z1 @z2 stkz1 stkz2)
      | Dict <- lemKnownSTK stky1
      , Dict <- lemKnownSTK stky2
      , Dict <- lemKnownSTK stkz1
      , Dict <- lemKnownSTK stkz2
      , Dict <- lemKnownSTKOfAD stkz1
      , Dict <- lemKnownSTKOfAD stkz2 ->
        let (c1, c2) = tunpair c
        in evalRev (evalRev s c1 (DeltaFromS @y1 @z1 $ DeltaProject1 d))
                   c2 (DeltaFromS @y2 @z2 $ DeltaProject2 d)
             -- TODO: costly
    _ -> error "evalRev: wrong tensor kinds"

  _ | Dict <- lemKnownSTKOfAD (knownSTK @y) ->
      case sameKnownSTS @y @(ADTensorKind y) of
        Just Refl -> evalRevSame s c d0
        _ -> s  -- the constructors remaining here have y that is a non-TKProduct
                -- so if y is equal to ADTensorKind y, the latter has
                -- the () scalar type and so no influence on the derivative.

evalRevSame
  :: forall y target.
     ( KnownSTK y, ADReadyNoLet target, ShareTensor target
     , y ~ ADTensorKind y )
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalRevSame !s !c = \case
  -- All constructors that only admit a non-TKProduct kind
  -- (and the DeltaInput constructor and the vector space constructors)
  -- can be handled here, where the extra
  -- constraint makes it easier.
  DeltaInput _ftk i ->
    let cs = Tensor knownSTK c
    in s {iMap = DMap.adjust (addTensorOrZero cs) i
                 $ iMap s}
    -- This and similar don't need to be runtime-specialized,
    -- because the type of c determines the Num instance for (+).
    -- Note that we can't express sharing by inserting DeltaShare constructors
    -- into iMap, because often sharing needs to work across many
    -- iMap keys. That's why global sharing is used.

  -- By placing these here, we force their derivatives to be zeroed
  -- whenever they are called on non-base types, which they should not ever be.
  -- This is ensured by the types of the three constructors, assuming that
  -- no Num instances are defined for the non-base type tensors.
  DeltaZero{} -> s
  DeltaScale k d -> evalRevSame s (k * c) d
  DeltaAdd d e -> let cShared = tshare c
              in evalRevSame (evalRevSame s cShared d) cShared e

  DeltaCastK @r1 d ->
    evalRev s (toADTensorKindShared (knownSTK @(TKScalar r1))
               $ kcast c) d

  DeltaCastR @r1 @_ @n d ->
    evalRevRuntimeSpecialized s (toADTensorKindShared (knownSTK @(TKR n r1))
                                 $ rcast c) d
  DeltaSum0R d -> case ftkDelta d of
    FTKR sh _ -> evalRevSame s (rreplicate0N sh c) d
  DeltaDot0R v vd ->
    evalRevSame s (v * rreplicate0N (rshape v) c) vd
      -- too slow: evalRevSame s (rmap0N (* (tscalar c)) v) vd
  DeltaIndexR d ix -> case ftkDelta d of
    FTKR sh _ | SNat <- shrRank sh ->
      evalRevSame s (roneHot (takeShape sh) c ix) d
  DeltaScatterR _sh d f -> case ftkDelta d of
    FTKR sh _ | SNat <- shrRank sh ->
      evalRevSame s (rgather sh c f) d
  DeltaGatherR _sh d f-> case ftkDelta d of
    FTKR sh _ | SNat <- shrRank sh ->
      evalRevSame s (rscatter sh c f) d
  DeltaAppendR d e -> case rshape c of
    n :$: _ -> let cShared = tshare c
                   k = case ftkDelta d of
                     FTKR ZSR _ -> error "evalRevSame: impossible pattern needlessly required"
                     FTKR (len :$: _) _ -> len
                   s2 = evalRevSame s (rslice 0 k cShared) d
               in evalRevSame s2 (rslice k (n - k) cShared) e
  DeltaSliceR i n d -> case tftk (knownSTK @y) c of
    FTKR (n' :$: rest) x ->
      assert (n' == n `blame` (n', n)) $
      let l = case ftkDelta d of
            FTKR ZSR _ -> error "evalRevSame: impossible pattern needlessly required"
            FTKR (len :$: _) _ -> len
      in evalRevSame s
               (rconcat $ NonEmpty.fromList
                  [ constantTarget 0 (FTKR (i :$: rest) x)
                  , c
                  , constantTarget 0 (FTKR (l - i - n :$: rest) x) ])
               d
    FTKR ZSR _ -> error "evalRevSame: impossible pattern needlessly required"
  DeltaReverseR d -> evalRevSame s (rreverse c) d
  DeltaTransposeR perm d ->
    let permR = permRInverse perm
    in evalRevSame s (rtranspose permR c) d
  DeltaReshapeR _sh d -> case ftkDelta d of
    FTKR sh _ | SNat <- shrRank sh ->
      evalRevSame s (rreshape sh c) d
  DeltaZipR d ->
    evalRevSame s (runzip c) d
  DeltaUnzipR d ->
    evalRevSame s (rzip c) d

  DeltaCastS @r1 @_ @sh d ->
    evalSRuntimeSpecialized s (toADTensorKindShared (knownSTK @(TKS sh r1))
                               $ scast c) d
  DeltaSum0S @_ @sh d | SNat <- shsProduct (knownShS @sh) ->
    evalRevSame s (sreplicate0N c) d
  DeltaDot0S @_ @sh v vd | SNat <- shsProduct (knownShS @sh) ->
    evalRevSame s (v * sreplicate0N c) vd
      -- too slow: evalRevSame s (smap0N (* (sscalar c)) v) vd
  DeltaIndexS d ix -> evalRevSame s (soneHot c ix) d
  DeltaScatterS @_ @_ @shm @shn @shp d f ->
    evalRevSame s (sgather @_ @_ @shm @shn @shp c f) d
  DeltaGatherS @_ @_ @shm @shn @shp d f ->
    evalRevSame s (sscatter @_ @_ @shm @shn @shp c f) d
  DeltaAppendS @_ @_ @m d e ->
    let cShared = tshare c
        s2 = evalRevSame s (sslice (Proxy @0) Proxy cShared) d
    in evalRevSame s2 (sslice (Proxy @m) Proxy cShared) e
  DeltaSliceS @_ @i d -> case tftk (knownSTK @y) c of
    FTKS _ x -> evalRevSame s (sappend @_ @_ @i
                              (constantTarget 0 (FTKS knownShS x))
                              (sappend
                                 c (constantTarget 0 (FTKS knownShS x)))) d
  DeltaReverseS d -> evalRevSame s (sreverse c) d
  DeltaTransposeS @perm @sh2 perm d ->
    withKnownShS (shsPermutePrefix perm (knownShS @sh2)) $
    permInverse perm $ \(permRev :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permR (Permutation.PermutePrefix perm sh2) :~: sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank (Permutation.PermutePrefix perm sh2) :~: Rank sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank permR :~: Rank perm)
        $ evalRevSame s (stranspose permRev c) d
  DeltaReshapeS d ->
    evalRevSame s (sreshape c) d
  DeltaZipS d ->
    evalRevSame s (sunzip c) d
  DeltaUnzipS d ->
    evalRevSame s (szip c) d

  DeltaCastX @r1 @_ @sh d ->
    evalXRuntimeSpecialized s (toADTensorKindShared (knownSTK @(TKX sh r1))
                               $ xcast c) d
  DeltaSum0X d -> case ftkDelta d of
    FTKX sh _ -> evalRevSame s (xreplicate0N sh c) d
  DeltaDot0X v vd ->
    evalRevSame s (v * xreplicate0N (xshape v) c) vd
      -- too slow: evalRevSame s (smap0N (* (sscalar c)) v) vd
  DeltaIndexX @sh1 @sh2 d ix -> case ftkDelta d of
    FTKX sh _ -> evalRevSame s (xoneHot (shxTakeSSX (Proxy @sh2) sh
                                                    (knownShX @sh1)) c ix) d
  DeltaScatterX @_ @_ @shm @shn @shp _sh d f -> case ftkDelta d of
    FTKX sh _ ->
      evalRevSame s (xgather @_ @_ @shm @shn @shp sh c f) d
  DeltaGatherX @_ @_ @shm @shn @shp _sh d f -> case ftkDelta d of
    FTKX sh _ ->
      evalRevSame s (xscatter @_ @_ @shm @shn @shp sh c f) d
  DeltaAppendX d e -> case (ftkDelta d, ftkDelta e) of
    ( FTKX shd@(Nested.SUnknown m :$% rest) _
     ,FTKX she@(Nested.SUnknown n :$% _) _ ) ->
      withSNat m $ \(SNat @m) -> withSNat n $ \(SNat @n) ->
      let cShared =
            tshare $ xmcast (ssxFromShape
                             $ Nested.SKnown (SNat @(m + n)) :$% rest) c
          s2 = evalRevSame s (xmcast (ssxFromShape shd)
                              $ xslice (Proxy @0) (Proxy @m) cShared) d
      in evalRevSame s2 (xmcast (ssxFromShape she)
                         $ xslice (Proxy @m) (Proxy @n) cShared) e
  DeltaSliceX @_ @i @n @k d -> case tftk (knownSTK @y) c of
    FTKX (_ :$% rest) x ->
      evalRevSame s
        (xmcast (ssxFromShape $ Nested.SKnown (SNat @(i + n + k)) :$% rest)
         $ xconcat $ NonEmpty.fromList
          [ constantTarget 0 (FTKX (Nested.SUnknown (valueOf @i) :$% rest) x)
          , xmcast (ssxFromShape $ Nested.SUnknown (valueOf @n) :$% rest) c
          , constantTarget 0 (FTKX (Nested.SUnknown (valueOf @k) :$% rest) x) ])
        d
  DeltaReverseX d -> evalRevSame s (xreverse c) d
  DeltaTransposeX @perm @sh2 perm d ->
    withKnownShX (ssxPermutePrefix perm (knownShX @sh2)) $
    permInverse perm $ \(permRev :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permR (Permutation.PermutePrefix perm sh2) :~: sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank (Permutation.PermutePrefix perm sh2) :~: Rank sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank permR :~: Rank perm)
        $ evalRevSame s (xtranspose permRev c) d
  DeltaReshapeX _sh d -> case ftkDelta d of
    FTKX sh _ -> evalRevSame s (xreshape sh c) d
  DeltaZipX d ->
    evalRevSame s (xunzip c) d
  DeltaUnzipX d ->
    evalRevSame s (xzip c) d

  DeltaSFromK d -> evalRevSame s (kfromS c) d
  DeltaSFromR @sh @x (DeltaFromS @y2 d) -> case sameKnownSTS @y2 @(TKS2 sh x) of
    Just Refl -> evalRevSame s c d
    _ -> error "evalRevSame: different shapes in DeltaSFromR(DeltaFromS)"
  DeltaSFromR d ->
    evalRevSame s (rfromS c) d
  DeltaSFromX @sh @_ @x (DeltaFromS @y2 d) -> case sameKnownSTS @y2 @(TKS2 sh x) of
    Just Refl -> evalRevSame s c d
    _ -> error "evalRevSame: different shapes in DeltaSFromX(DeltaFromS)"
  DeltaSFromX d ->
    evalRevSame s (xfromS c) d

  DeltaXNestR d ->
    evalRevSame s (xunNestR c) d
  DeltaXNestS d ->
    evalRevSame s (xunNestS c) d
  DeltaXNest d ->
    evalRevSame s (xunNest c) d
  DeltaXUnNestR d ->
    evalRevSame s (xnestR knownShX c) d
  DeltaXUnNestS d ->
    evalRevSame s (xnestS knownShX c) d
  DeltaXUnNest d ->
    evalRevSame s (xnest knownShX c) d

  d -> evalRev s c d
    -- the remaining constructors are already handled in evalRev, so let's use that

evalRevFromnMap :: forall target. (ADReadyNoLet target, ShareTensor target)
             => EvalState target -> EvalState target
evalRevFromnMap s@EvalState{nMap, dMap} =
  -- We discharge the non-vector cases before the vector ones, because
  -- the latter tend to create and store more cases and so enlarge
  -- the working set of cases.
  case DMap.maxViewWithKey nMap of
    Just (n@(NodeId @_ @y _) :=> d, nMap2) ->
      let s2 = s {nMap = nMap2}
          errorMissing :: a
          errorMissing = error $ "evalRevFromnMap: missing cotangent " ++ show n
          s3 = case knownSTK @y of
            STKR @n SNat (STKScalar @r _) -> case DMap.lookup n dMap of
              Just (Cotangent c) -> evalRevRuntimeSpecialized @n @r s2 c d
              Nothing -> errorMissing
            STKS @sh sh (STKScalar @r _) ->
              withKnownShS sh $ case DMap.lookup n dMap of
                Just (Cotangent c) -> evalSRuntimeSpecialized @sh @r s2 c d
                Nothing -> errorMissing
            STKX @sh sh (STKScalar @r _) ->
              withKnownShX sh $ case DMap.lookup n dMap of
                Just (Cotangent c) -> evalXRuntimeSpecialized @sh @r s2 c d
                Nothing -> errorMissing
            _ -> case DMap.lookup n dMap of
              Just (Cotangent c) -> evalRev s2 c d
              Nothing -> errorMissing
      in evalRevFromnMap s3
    Nothing -> s  -- loop ends

{-
        -- The general case is given as the last one below,
        -- but for a few constructors it's faster to inline @evalRev@ instead.
        -- BTW, such an optimization doesn't really belong in the simplified
        -- horde-ad and no consistent benefit should be expected here.
        DeltaIndex0 ZeroR{} _ _ -> s  -- shortcut
        DeltaIndex0 (InputR i) ixs' sh ->
          let ixs = indexToList ixs'
              f v = if isTensorDummy v
                    then treplicate0ND sh 0 `OD.update` [(ixs, c)]
                    else v `OD.update` [(ixs, v `rindex0D` ixs + c)]
          in s {iMap = DMap.adjust f i $ iMap s}
        DeltaIndex0 (ShareR n d) ixs' sh ->
          let ixs = indexToList ixs'
          in case DMap.lookup n $ nMap s of
            Just (DynamicRanked _) ->
              let f v = v `OD.update` [(ixs, v `rindex0D` ixs + c)]
              in s {dMap = DMap.adjust f n $ dMap s}
                -- This would be an asymptotic optimization compared to
                -- the general case below, if not for the non-mutable update,
                -- which implies copying the whole @v@ vector,
                -- so it's only several times faster (same allocation,
                -- but not adding to each cell of @v@).
            Nothing ->
              let v = treplicate0ND sh 0 `OD.update` [(ixs, c)]
              in s { nMap = DMap.insert n (DynamicRanked d) $ nMap s
                   , dMap = DMap.insert n v $ dMap s }
            _ -> error "evalRevFromnMap: corrupted nMap"
-}


-- * Forward derivative computation from the delta expressions

-- | Forward derivative computation via forward-evaluation of delta-expressions
-- (which is surprisingly competitive to the direct forward method,
-- until the allocation of deltas gets large enough to affect cache hits).
-- This is the directional derivative, calculated for the point,
-- at which the delta expression was computed (which is the point
-- represented by the parameters of the objective function and used
-- to compute it's dual number result) and along the direction vector(s)
-- given in the last parameter called @ds@.
--
-- This mimics the reverse derivative code, but in reverse. Perhaps this can be
-- simplified, but the obvious simplest formulation does not honour sharing
-- and evaluates shared subexpressions repeatedly, so this state-passing
-- formulation is adopted.
evalFwd
  :: forall target y.
     (ADReadyNoLet target, ShareTensor target, KnownSTK y)
  => IMap target -> ADMap target -> Delta target y
  -> (ADMap target, target (ADTensorKind y))
evalFwd params s d0 = case d0 of
  DeltaPair @y1 @y2 d1 d2 | Dict <- lemKnownSTKOfAD (knownSTK @y1)
                      , Dict <- lemKnownSTKOfAD (knownSTK @y2) ->
    let (s2, t) = evalFwd params s d1
        (s3, u) = evalFwd params s2 d2
    in (s3, tpair t u)
  DeltaProject1 @_ @z d | Dict <- lemKnownSTKOfAD (knownSTK @y)
                    , Dict <- lemKnownSTKOfAD (knownSTK @z) ->
    let (s2, v) = evalFwd params s d
    in (s2, tproject1 v)
  DeltaProject2 @x d | Dict <- lemKnownSTKOfAD (knownSTK @y)
                 , Dict <- lemKnownSTKOfAD (knownSTK @x) ->
    let (s2, v) = evalFwd params s d
    in (s2, tproject2 v)
  DeltaFromVector snat stk lsd | Refl <- lemBuildOfAD snat stk ->
    let (s2, l) = mapAccumL (evalFwd params) s lsd
    in (s2, tfromVectorShare snat (adSTK stk) l)
  DeltaSum snat stk d | Refl <- lemBuildOfAD snat stk ->
    let (s2, t) = evalFwd params s d
    in (s2, tsumShare snat (adSTK stk) t)
  DeltaReplicate snat stk d | Refl <- lemBuildOfAD snat stk ->
    let (s2, t) = evalFwd params s d
    in (s2, treplicateShare snat (adSTK stk) t)
  DeltaMapAccumR @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            df _rf acc0' es'
   | Dict <- lemKnownSTKOfAD (knownSTK @accShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @bShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @eShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @accShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @eShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @(ADTensorKind accShs))
   , Dict <- lemKnownSTKOfBuild k (knownSTK @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (knownSTK @bShs)
   , Refl <- lemBuildOfAD k (knownSTK @eShs) ->
    let accShsAD = adFTK accShs
        bShsAD = adFTK bShs
        eShsAD = adFTK eShs
        (s2, cacc0) = evalFwd params s acc0'
        (s3, ces) = evalFwd params s2 es'
    in (s3, tmapAccumR (Proxy @target)
                       k accShsAD bShsAD (FTKProduct eShsAD
                                                     (FTKProduct accShs eShs))
                       (\dacc de_acc_e ->
                        tlet de_acc_e $ \ !de_acc_e1 ->
                          unHFun df (tpair (tpair dacc (tproject1 de_acc_e1))
                                           (tproject2 de_acc_e1)))
                       cacc0
                       (tpair ces (tpair q es)))
  DeltaMapAccumL @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            df _rf acc0' es'
   | Dict <- lemKnownSTKOfAD (knownSTK @accShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @bShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @eShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @accShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @eShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @(ADTensorKind accShs))
   , Dict <- lemKnownSTKOfBuild k (knownSTK @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (knownSTK @bShs)
   , Refl <- lemBuildOfAD k (knownSTK @eShs) ->
    let accShsAD = adFTK accShs
        bShsAD = adFTK bShs
        eShsAD = adFTK eShs
        (s2, cacc0) = evalFwd params s acc0'
        (s3, ces) = evalFwd params s2 es'
    in (s3, tmapAccumL (Proxy @target)
                       k accShsAD bShsAD (FTKProduct eShsAD
                                                     (FTKProduct accShs eShs))
                       (\dacc de_acc_e ->
                        tlet de_acc_e $ \ !de_acc_e1 ->
                          unHFun df (tpair (tpair dacc (tproject1 de_acc_e1))
                                           (tproject2 de_acc_e1)))
                       cacc0
                       (tpair ces (tpair q es)))

  DeltaShare n d | Dict <- lemKnownSTKOfAD (knownSTK @y) ->
    case DMap.lookup n s of
      Just e1 -> (s, unCotangent e1)
      Nothing ->
        let (s2, cRaw) = evalFwd params s d
            cShared = tshare cRaw
            cd = Cotangent cShared
              -- cRaw is shared, because it's put into the map and then
              -- potentially looked up many times, so it'd get duplicated
            s3 = DMap.insert n cd s2
        in (s3, cShared)
  DeltaInput _ftk inputId ->
    case DMap.lookup inputId params of
      Just dtk -> (s, toADTensorKindShared knownSTK $ evalTensorOrZero dtk)
      Nothing -> error "evalFwd: missing input"


  DeltaFromS @_ @z (DeltaSFromR @sh @x d)
    | Just Refl <- sameSTK (adSTK (knownSTK @z))
                           (adSTK (knownSTK @(TKR2 (Rank sh) x))) ->
      evalFwd params s d
  DeltaFromS @_ @z (DeltaSFromX @_ @sh' @x d)
    | Just Refl <- sameSTK (adSTK (knownSTK @z))
                           (adSTK (knownSTK @(TKX2 sh' x))) ->
      evalFwd params s d
  DeltaFromS @y2 @z d | Dict <- lemKnownSTKOfAD (knownSTK @y2)
                 , Dict <- lemKnownSTKOfAD (knownSTK @z) ->
    second tfromSShare $ evalFwd params s d

  _ | Dict <- lemKnownSTKOfAD (knownSTK @y) ->
      case sameKnownSTS @y @(ADTensorKind y) of
        Just Refl -> evalFwdSame params s d0
        _ -> (s, constantTarget 0 $ adFTK $ ftkDelta d0)

evalFwdSame
  :: forall target y.
     ( KnownSTK y, ADReadyNoLet target, ShareTensor target
     , y ~ ADTensorKind y )
  => IMap target -> ADMap target -> Delta target y
  -> (ADMap target, target (ADTensorKind y))
evalFwdSame params s = \case
  DeltaInput _ftk inputId ->
    case DMap.lookup inputId params of
      Just dtk -> (s, evalTensorOrZero dtk)
      Nothing -> error "evalFwdSame: missing input"

  -- See the comment about these three in evalRevSame.
  DeltaZero ftk -> (s, constantTarget 0 $ adFTK ftk)
  DeltaScale k d -> second (* k) $ evalFwdSame params s d
  DeltaAdd d e -> let (s2, t) = evalFwdSame params s d
                      (s3, u) = evalFwdSame params s2 e
                  in (s3, t + u)

  d0@(DeltaCastK @r1 d) ->
    case sameSTK (STKScalar (typeRep @r1)) (adSTK (STKScalar (typeRep @r1))) of
      Just Refl -> second kcast $ evalFwdSame params s d
      _ -> (s, constantTarget 0 $ adFTK $ ftkDelta d0)

  d0@(DeltaCastR @r1 @_ @n d) ->
    case sameSTK (knownSTK @(TKR n r1))
                 (adSTK ((knownSTK @(TKR n r1)))) of
      Just Refl -> second rcast $ evalFwdSame params s d
      _ -> (s, constantTarget 0 $ adFTK $ ftkDelta d0)
  DeltaSum0R (DeltaZero (FTKR _ x)) -> (s, constantTarget 0 (FTKR ZSR x))
  DeltaSum0R d -> second rsum0 $ evalFwdSame params s d
  DeltaDot0R _ DeltaZero{} -> (s, rscalar 0)
  DeltaDot0R v d -> second (rdot0 v) $ evalFwdSame params s d
  DeltaIndexR d ix -> second (`rindex` ix) $ evalFwdSame params s d
  DeltaScatterR sh d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, rscatter sh t f)
  DeltaGatherR sh d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, rgather sh t f)
  DeltaAppendR d e ->
    let (s2, t) = evalFwdSame params s d
        (s3, u) = evalFwdSame params s2 e
    in (s3, rappend t u)
  DeltaSliceR i n d -> second (rslice i n) $ evalFwdSame params s d
  DeltaReverseR d -> second rreverse $ evalFwdSame params s d
  DeltaTransposeR perm d -> second (rtranspose perm) $ evalFwdSame params s d
  DeltaReshapeR sh d -> second (rreshape sh) $ evalFwdSame params s d
  DeltaZipR d -> second rzip $ evalFwdSame params s d
  DeltaUnzipR d -> second runzip $ evalFwdSame params s d
-- Not needed, because we take only the i-th component of the vector,
-- so v is not copied.
--  in (s2, rfromD $ tunvector v) V.! i)

  d0@(DeltaCastS @r1 @_ @sh d) ->
    case sameSTK (knownSTK @(TKS sh r1))
                 (adSTK ((knownSTK @(TKS sh r1)))) of
      Just Refl -> second scast $ evalFwdSame params s d
      _ -> (s, constantTarget 0 $ adFTK $ ftkDelta d0)
  DeltaSum0S (DeltaZero (FTKS _ x)) -> (s, constantTarget 0 (FTKS ZSS x))
  DeltaSum0S d -> second ssum0 $ evalFwdSame params s d
  DeltaDot0S _ DeltaZero{} -> (s, srepl 0)
  DeltaDot0S v d -> second (sdot0 v) $ evalFwdSame params s d
  DeltaIndexS d ix -> second (`sindex` ix) $ evalFwdSame params s d
  DeltaScatterS @_ @_ @shm @shn @shp d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, sscatter @_ @_ @shm @shn @shp t f)
  DeltaGatherS @_ @_ @shm @shn @shp d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, sgather @_ @_ @shm @shn @shp t f)
  DeltaAppendS d e ->
    let (s2, t) = evalFwdSame params s d
        (s3, u) = evalFwdSame params s2 e
    in (s3, sappend t u)
  DeltaSliceS @_ @i d -> second (sslice (Proxy @i) Proxy) $ evalFwdSame params s d
  DeltaReverseS d -> second sreverse $ evalFwdSame params s d
  DeltaTransposeS perm d -> second (stranspose perm)
                       $ evalFwdSame params s d
  DeltaReshapeS d -> second sreshape $ evalFwdSame params s d
  DeltaZipS d -> second szip $ evalFwdSame params s d
  DeltaUnzipS d -> second sunzip $ evalFwdSame params s d
-- Not needed, because we take only the i-th component of the vector,
-- so v is not copied.
--  in (s2, sfromD $ tunvector v V.! i)

  d0@(DeltaCastX @r1 @_ @sh d) ->
    case sameSTK (knownSTK @(TKX sh r1))
                 (adSTK ((knownSTK @(TKX sh r1)))) of
      Just Refl -> second xcast $ evalFwdSame params s d
      _ -> (s, constantTarget 0 $ adFTK $ ftkDelta d0)
  DeltaSum0X (DeltaZero (FTKX _ x)) -> (s, constantTarget 0 (FTKX ZSX x))
  DeltaSum0X d -> second xsum0 $ evalFwdSame params s d
  DeltaDot0X _ DeltaZero{} -> (s, xrepl ZSX 0)
  DeltaDot0X v d -> second (xdot0 v) $ evalFwdSame params s d
  DeltaIndexX d ix -> second (`xindex` ix) $ evalFwdSame params s d
  DeltaScatterX @_ @_ @shm @shn @shp sh d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, xscatter @_ @_ @shm @shn @shp sh t f)
  DeltaGatherX @_ @_ @shm @shn @shp sh d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, xgather @_ @_ @shm @shn @shp sh t f)
  DeltaAppendX d e ->
    let (s2, t) = evalFwdSame params s d
        (s3, u) = evalFwdSame params s2 e
    in (s3, xappend t u)
  DeltaSliceX @_ @i d -> second (xslice (Proxy @i) Proxy) $ evalFwdSame params s d
  DeltaReverseX d -> second xreverse $ evalFwdSame params s d
  DeltaTransposeX perm d -> second (xtranspose perm)
                       $ evalFwdSame params s d
  DeltaReshapeX sh2 d -> second (xreshape sh2) $ evalFwdSame params s d
  DeltaZipX d -> second xzip $ evalFwdSame params s d
  DeltaUnzipX d -> second xunzip $ evalFwdSame params s d

  DeltaSFromK d -> let (s2, t) = evalFwdSame params s d
                   in (s2, sfromK t)
  DeltaSFromR @sh @x (DeltaFromS @y2 d) -> case sameKnownSTS @y2 @(TKS2 sh x) of
    Just Refl -> evalFwdSame params s d
    _ -> error "evalFwdSame: different shapes in DeltaSFromR(DeltaFromS)"
  DeltaSFromR d -> second sfromR $ evalFwdSame params s d
  DeltaSFromX @sh @_ @x (DeltaFromS @y2 d) -> case sameKnownSTS @y2 @(TKS2 sh x) of
    Just Refl -> evalFwdSame params s d
    _ -> error "evalFwdSame: different shapes in DeltaSFromX(DeltaFromS)"
  DeltaSFromX d -> second sfromX $ evalFwdSame params s d

  DeltaXNestR d -> second (xnestR knownShX) $ evalFwdSame params s d
  DeltaXNestS d -> second (xnestS knownShX) $ evalFwdSame params s d
  DeltaXNest d -> second (xnest knownShX) $ evalFwdSame params s d
  DeltaXUnNestR d -> second xunNestR $ evalFwdSame params s d
  DeltaXUnNestS d -> second xunNestS $ evalFwdSame params s d
  DeltaXUnNest d -> second xunNest $ evalFwdSame params s d

  d -> evalFwd params s d
