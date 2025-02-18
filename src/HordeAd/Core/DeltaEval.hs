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
import Data.Proxy (Proxy (Proxy))
import Data.Traversable (mapAccumL)
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Text.Show (showListWith)
import Text.Show.Functions ()
import Type.Reflection (typeRep)

import Data.Array.Mixed.Permutation (permInverse)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (ssxFromShape, withKnownShX)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested (Rank, ShR (..), ShS (..), ShX (..), type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape
  (ixrRank, shrRank, shsRank, withKnownShS)

import HordeAd.Core.Delta
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

-- * Computing derivatives from delta expressions

gradientFromDelta
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => FullTensorKind x
  -> target (ADTensorKind z)
  -> Delta target z
  -> target (ADTensorKind x)
gradientFromDelta !parameters0 !dt deltaTopLevel =
  let s0 = initEvalState parameters0
      s1 = evalRev s0 dt deltaTopLevel
      s2 = evalRevFromnMap s1
      (res, remainder) =
        rebuildInputs @(ADTensorKind x) (DMap.toAscList $ iMap s2) s2
        $ adFTK parameters0
  in assert (null remainder) res

derivativeFromDelta
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => Delta target z -> FullTensorKind (ADTensorKind x)
  -> target (ADTensorKind x)
  -> target (ADTensorKind z)
derivativeFromDelta deltaTopLevel ftk ds =
    let iMap = DMap.fromDistinctAscList $ fst $ generateDSums 0 ftk ds
        s0 = DMap.empty
        !(!_s2, !c) = evalFwd iMap s0 deltaTopLevel
    in c


-- * Auxiliary datatypes for Delta evaluation

type ADMap target = DEnumMap (NodeId target) (Cotangent target)

type IMap target = DEnumMap (InputId target) (TensorOrZero target)

showsPrec_IMap
  :: (forall y. KnownSTK y => Show (TensorOrZero target y))
  => Int -> IMap target -> ShowS
showsPrec_IMap d demap =
  showParen (d > 10) $
    showString "fromList "
    . showListWith
        (\(k :=> target) ->
          withKnownSTK (inputIdToSTK k) $
          showsPrec 2 k . showString " :=> " . showsPrec 1 target)
        (DMap.toList demap)

show_IMap
  :: (forall y. KnownSTK y => Show (TensorOrZero target y))
  => IMap target -> String
show_IMap iMap = showsPrec_IMap 0 iMap ""

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
    TOTensor (target y)
  | TOZero (FullTensorKind y)
  deriving Show

evalTensorOrZero :: forall target x. ADReadyNoLet target
                 => TensorOrZero target x -> target x
evalTensorOrZero = \case
  TOTensor t -> t
  TOZero ftk -> constantTarget 0 ftk

addTensorOrZero :: forall target y. ADReadyNoLet target
                => STensorKind y
                -> TensorOrZero target y -> TensorOrZero target y
                -> TensorOrZero target y
addTensorOrZero stk a b = case (a, b) of
  (TOTensor ta, TOTensor tb) -> TOTensor $ addTarget stk ta tb
    -- target has a ShareTensor instance, so ta and tb don't need
    -- to be duplicable
  (TOZero{}, _) -> b
  (_, TOZero{}) -> a

-- Matches generateDSumsDummy.
rebuildInputs :: forall ady target. ADReadyNoLet target
              => [DSum (InputId target) (TensorOrZero target)]
              -> EvalState target  -- original state; only for error messages
              -> FullTensorKind ady
              -> (target ady, [DSum (InputId target) (TensorOrZero target)])
rebuildInputs els s2 ftk = case ftk of
  FTKProduct ftk1 ftk2 ->
      let (t1, rest1) = rebuildInputs els s2 ftk1
          (t2, rest2) = rebuildInputs rest1 s2 ftk2
          !t = tpair t1 t2
      in (t, rest2)
  _ -> case els of
    (n :=> tz@(TOTensor t)) : rest ->
      case sameSTK (inputIdToSTK n) (ftkToSTK ftk) of
        Just Refl ->
          (t, rest)
        _ | Dict <- lemKnownSTK (inputIdToSTK n) ->
          error $ "rebuildInputs: wrong Tensor type: "
                  ++ show (n, tz, show_IMap (iMap s2))
    (n :=> tz@(TOZero ftk2)) : rest ->
      case matchingFTK ftk2 ftk of
        Just Refl ->
          let !zero = constantTarget 0 ftk
          in (zero, rest)
          -- TODO: actually pass this ZERO through to optimizers
          -- and use there to avoid updating the gradient
          -- and maybe use elsewhere, too.
        _ | Dict <- lemKnownSTK (inputIdToSTK n) ->
          error $ "rebuildInputs: wrong Zero type: "
                  ++ show (n, tz, show_IMap (iMap s2))
    _ -> error $ "rebuildInputs: illegal TensorOrZero: "
                 ++ show_IMap (iMap s2)

-- Matches generateDeltaInputs.
generateDSumsDummy :: Int -> FullTensorKind y
                   -> ([DSum (InputId target) (TensorOrZero target)], Int)
generateDSumsDummy j ftk  = case ftk of
  FTKProduct ftk1 ftk2 ->
    let (ds1, j1) = generateDSumsDummy j ftk1
        (ds2, j2) = generateDSumsDummy j1 ftk2
    in (ds1 ++ ds2, j2)
  _ -> ([mkInputId (ftkToSTK ftk) j :=> TOZero ftk], j + 1)

-- Matches generateDeltaInputs.
generateDSums :: ShareTensor target
              => Int -> FullTensorKind y -> target y
              -> ([DSum (InputId target) (TensorOrZero target)], Int)
generateDSums j ftk t = case ftk of
  FTKProduct ftk1 ftk2 ->
    let (t1, t2) = tunpair t
        (ds1, j1) = generateDSums j ftk1 t1
        (ds2, j2) = generateDSums j1 ftk2 t2
    in (ds1 ++ ds2, j2)
  _ -> ([mkInputId (ftkToSTK ftk) j :=> TOTensor t], j + 1)

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
initEvalState :: FullTensorKind x -> EvalState target
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
      iMap = DMap.fromDistinctAscList $ fst $ generateDSumsDummy 0 $ adFTK ftk0
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
     (GoodScalar r, ADReadyNoLet target, ShareTensor target)
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
     (GoodScalar r, ADReadyNoLet target, ShareTensor target)
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
     (GoodScalar r, ADReadyNoLet target, ShareTensor target)
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
     (ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalRev !s !c d0 = case d0 of
  -- All constructors that admit a TKProduct kind need to be handled in evalRev
  -- except for DeltaInput that is always constructed only in basic kinds.
  DeltaPair d1 d2 ->
    let (c1, c2) = tunpair c
    in evalRev (evalRev s c1 d1) c2 d2
  DeltaProject1 d -> case ftkDelta d of
    FTKProduct _ ftk2 ->
      let zero = constantTarget 0 $ adFTK ftk2
      in evalRev s (tpair c zero) d
    -- if y is, e.g., TKR Int 0, we eval this delta even though we could ignore it
    -- at the price of complicating or duplicating the code slightly more
  DeltaProject2 d -> case ftkDelta d of
    FTKProduct ftk1 _ ->
      let zero = constantTarget 0 $ adFTK ftk1
      in evalRev s (tpair zero c) d
  DeltaFromVector snat stk ld | Refl <- lemBuildOfAD snat stk ->
    let cShared = tshare c
        cxs = tunravelToListShare snat (adSTK stk) cShared
    in foldl' (\ !s2 (cx, d2) -> evalRev s2 cx d2) s
       $ zip cxs (V.toList ld)
  DeltaSum snat stk d | Refl <- lemBuildOfAD snat stk ->
    evalRev s (treplicateShare snat (adSTK stk) c) d
  DeltaReplicate snat stk d | Refl <- lemBuildOfAD snat stk ->
    evalRev s (tsumShare snat (adSTK stk) c) d
  DeltaMapAccumR k bShs eShs q es _df rf acc0' es'
   | Refl <- lemBuildOfAD k (ftkToSTK bShs)
   , Refl <- lemBuildOfAD k (ftkToSTK eShs) ->
    let accShs = ftkDelta acc0'
        accShsAD = adFTK accShs
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
  DeltaMapAccumL k bShs eShs q es _df rf acc0' es'
   | Refl <- lemBuildOfAD k (ftkToSTK bShs)
   , Refl <- lemBuildOfAD k (ftkToSTK eShs) ->
    let accShs = ftkDelta acc0'
        accShsAD = adFTK accShs
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

  DeltaShare n d ->
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
    $ if DMap.member n $ nMap s
      then let addc x = Cotangent $ addTarget (adSTK $ ftkToSTK $ ftkDelta d)
                                              c (unCotangent x)
             -- target has a ShareTensor instance, so addTarget arguments
             -- don't need to be duplicable
           in s {dMap = DMap.adjust addc n $ dMap s}
      else let cd = Cotangent c
           in s { nMap = DMap.insert n d $ nMap s
                , dMap = DMap.insert n cd $ dMap s }

  DeltaFromS stk (DeltaSFromR _ d)
    | y2 <- ftkDelta d
    , Just Refl <- sameSTK (adSTK stk) (adSTK $ ftkToSTK y2) ->
      evalRev s c d
  DeltaFromS stk (DeltaSFromX _ d)
    | y2 <- ftkDelta d
    , Just Refl <- sameSTK (adSTK stk) (adSTK $ ftkToSTK y2) ->
      evalRev s c d
  DeltaFromS stk d -> case (ftkToSTK $ ftkDelta d, stk) of
    (stky, stkz) | Just Refl <- sameSTK stky stkz -> evalRev s c d
    (STKS ZSS yx@(STKScalar @ry), STKScalar @rz) ->
      case testEquality (typeRep @ry) (typeRep @rz) of
        Just Refl -> case sameSTK yx (adSTK yx) of
          Just Refl -> evalRev s (sfromK c) d
          _ -> s
        Nothing -> error "evalRev: tensor kinds don't match"
    (STKS shy yx, STKR nx zx) | Dict <- lemKnownSTKOfAD yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) nx) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          evalRev s (sfromR c) d
        _ -> error "evalRev: tensor kinds don't match"
    (STKS shy yx, STKX shx zx) | Dict <- lemKnownSTKOfAD yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) (ssxRank shx)) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          evalRev s (sfromX c) d
        _ -> error "evalRev: tensor kinds don't match"
    (STKProduct{}, STKProduct stkz1 stkz2) ->
        let (c1, c2) = tunpair c
        in evalRev (evalRev s c1 (DeltaFromS stkz1 $ DeltaProject1 d))
                   c2 (DeltaFromS stkz2 $ DeltaProject2 d)
             -- TODO: costly
    _ -> error "evalRev: wrong tensor kinds"

  _ -> case ftkDelta d0 of
    y -> case matchingFTK y (adFTK y) of
        Just Refl -> evalRevSame s c d0
        _ -> s  -- the constructors remaining here have y that is a non-TKProduct
                -- so if y is equal to ADTensorKind y, the latter has
                -- the () scalar type and so no influence on the derivative.

evalRevSame
  :: forall y target.
     (ADReadyNoLet target, ShareTensor target, y ~ ADTensorKind y)
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalRevSame !s !c = \case
  -- All constructors that only admit a non-TKProduct kind
  -- (and the DeltaInput constructor and the vector space constructors)
  -- can be handled here, where the extra
  -- constraint makes it easier.
  DeltaInput ftk i ->
    let cs = TOTensor c
    in s {iMap = DMap.adjust (addTensorOrZero (ftkToSTK ftk) cs) i
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
  DeltaAdd d e ->
    let cShared = tshare c
    in evalRevSame (evalRevSame s cShared d) cShared e

  DeltaCastK @r1 d ->
    evalRev s (toADTensorKindShared (STKScalar @r1) $ kcast c) d

  DeltaCastR d -> case ftkDelta d of
    y ->
      evalRevRuntimeSpecialized
      s (toADTensorKindShared (ftkToSTK y) $ rcast c) d
  DeltaSum0R d -> case ftkDelta d of
    FTKR sh x | SNat <- shrRank sh ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (rreplicate0N sh c) d
  DeltaDot0R v d -> case ftkDelta d of
    FTKR sh x | SNat <- shrRank sh ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (v * rreplicate0N (rshape v) c) d
        -- too slow: evalRevSame s (rmap0N (* (tscalar c)) v) vd
  DeltaIndexR SNat d ix -> case ftkDelta d of
    FTKR sh x | SNat <- ixrRank ix ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (roneHot (takeShape sh) c ix) d  -- TODO: ixrToShR ix
  DeltaScatterR SNat SNat SNat _sh d f -> case ftkDelta d of
    FTKR sh x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (rgather sh c f) d
  DeltaGatherR SNat SNat SNat _sh d f -> case ftkDelta d of
    FTKR sh x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (rscatter sh c f) d
  DeltaAppendR d e -> case (ftkDelta d, ftkDelta e) of
    (FTKR (m :$: _) x, FTKR (n :$: _) _) ->
      withKnownSTK (ftkToSTK x) $
      let cShared = tshare c
          s2 = evalRevSame s (rslice 0 m cShared) d
      in evalRevSame s2 (rslice m n cShared) e
    _ -> error "evalRevSame: impossible pattern needlessly required"
  DeltaSliceR i n d -> case ftkDelta d of
    FTKR (l :$: rest) x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s
               (rconcat $ NonEmpty.fromList
                  [ constantTarget 0 (FTKR (i :$: rest) x)
                  , c
                  , constantTarget 0 (FTKR (l - i - n :$: rest) x) ])
               d
    FTKR ZSR _ -> error "evalRevSame: impossible pattern needlessly required"
  DeltaReverseR d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (rreverse c) d
  DeltaTransposeR perm d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      let permR = permRInverse perm
      in evalRevSame s (rtranspose permR c) d
  DeltaReshapeR _sh2 d -> case ftkDelta d of
    FTKR sh x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (rreshape sh c) d
  DeltaZipR d -> evalRevSame s (runzip c) d
  DeltaUnzipR d -> evalRevSame s (rzip c) d

  DeltaCastS d -> case ftkDelta d of
    y ->
      evalSRuntimeSpecialized
      s (toADTensorKindShared (ftkToSTK y) $ scast c) d
  DeltaSum0S d -> case ftkDelta d of
    FTKS sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS sh $
      evalRevSame s (sreplicate0N c) d
  DeltaDot0S v d -> case ftkDelta d of
    FTKS sh FTKScalar ->
      withKnownShS sh $
      evalRevSame s (v * sreplicate0N c) d
        -- too slow: evalRevSame s (smap0N (* (sscalar c)) v) vd
  DeltaIndexS shn d ix -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS shn $
      withKnownShS (ixsToShS ix) $
      evalRevSame s (soneHot c ix) d
  DeltaScatterS @shm @shn shm shn shp d f -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS shm $
      withKnownShS shn $
      withKnownShS shp $
      evalRevSame s (sgather @_ @_ @shm @shn c f) d
  DeltaGatherS @shm @shn shm shn shp d f -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS shm $
      withKnownShS shn $
      withKnownShS shp $
      evalRevSame s (sscatter @_ @_ @shm @shn c f) d
  DeltaAppendS d e -> case (ftkDelta d, ftkDelta e) of
    (FTKS (msnat :$$ _) x, FTKS (_ :$$ _) _) ->
      withKnownSTK (ftkToSTK x) $
      let cShared = tshare c
          s2 = evalRevSame s (sslice (SNat @0) SNat SNat cShared) d
      in evalRevSame s2 (sslice msnat SNat SNat cShared) e
  DeltaSliceS i@SNat _ k@SNat d -> case ftkDelta d of
    FTKS (_ :$$ sh) x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (sappend
                       (constantTarget 0 (FTKS (i :$$ sh) x))
                          (sappend
                            c (constantTarget 0 (FTKS (k :$$ sh) x)))) d
  DeltaReverseS d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (sreverse c) d
  DeltaTransposeS @perm @sh2 perm d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      permInverse perm $ \(permRev :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permR (Permutation.PermutePrefix perm sh2) :~: sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank (Permutation.PermutePrefix perm sh2) :~: Rank sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank permR :~: Rank perm)
        $ evalRevSame s (ttranspose permRev c) d
  DeltaReshapeS _sh2 d -> case ftkDelta d of
    FTKS sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS sh $
      evalRevSame s (sreshape c) d
  DeltaZipS d -> evalRevSame s (sunzip c) d
  DeltaUnzipS d -> evalRevSame s (szip c) d

  DeltaCastX d -> case ftkDelta d of
    y ->
      evalXRuntimeSpecialized
      s (toADTensorKindShared (ftkToSTK y) $ xcast c) d
  DeltaSum0X d -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX (ssxFromShape sh) $
      evalRevSame s (xreplicate0N sh c) d
  DeltaDot0X v d -> case ftkDelta d of
    FTKX sh FTKScalar ->
      withKnownShX (ssxFromShape sh) $
      evalRevSame s (v * xreplicate0N (xshape v) c) d
        -- too slow: evalRevSame s (smap0N (* (sscalar c)) v) vd
  DeltaIndexX @shm @shn shn d ix -> case ftkDelta d of
    FTKX sh x | SNat @len <- ixxRank ix ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX shn $
      withKnownShX (ssxFromShape sh) $
      withKnownShX (ssxTakeIx @shm @shn (ssxFromShape sh) ix) $
      gcastWith (unsafeCoerceRefl :: Take (Rank shm) (shm ++ shn) :~: shm) $
      evalRevSame s (xoneHot (takeShX @len sh) c ix) d
--TODO      evalRevSame s (xoneHot (shxTakeSSX (Proxy @shn) sh
--                                         (ixxToSSX ix)) c ix) d
  DeltaScatterX @shm @shn shm shn shp _sh d f -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX shm $
      withKnownShX shn $
      withKnownShX shp $
      evalRevSame s (xgather @_ @_ @shm @shn sh c f) d
  DeltaGatherX @shm @shn shm shn shp _sh d f -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX shm $
      withKnownShX shn $
      withKnownShX shp $
      evalRevSame s (xscatter @_ @_ @shm @shn sh c f) d
  DeltaAppendX d e -> case (ftkDelta d, ftkDelta e) of
    (FTKX (Nested.SKnown m@SNat :$% _) x, FTKX (Nested.SKnown SNat :$% _) _) ->
      withKnownSTK (ftkToSTK x) $
      let cShared = tshare c
          s2 = evalRevSame s (xslice (SNat @0) SNat SNat cShared) d
      in evalRevSame s2 (xslice m SNat SNat cShared) e
  DeltaSliceX i@SNat _ k@SNat d -> case ftkDelta d of
    FTKX (_ :$% sh) x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (xappend
                       (constantTarget 0 (FTKX (Nested.SKnown i :$% sh) x))
                          (xappend
                            c (constantTarget
                                 0 (FTKX (Nested.SKnown k :$% sh) x)))) d
  DeltaReverseX d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (xreverse c) d
  DeltaTransposeX @perm @sh2 perm d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      permInverse perm $ \(permR :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permR (Permutation.PermutePrefix perm sh2) :~: sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Rank (Permutation.PermutePrefix perm sh2) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Rank permR :~: Rank perm) $
        withKnownPerm permR $
        evalRevSame s (xtranspose @_ @permR c) d
  DeltaReshapeX _sh2 d -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (xreshape sh c) d
  DeltaZipX d -> evalRevSame s (xunzip c) d
  DeltaUnzipX d -> evalRevSame s (xzip c) d

  DeltaSFromK d -> evalRevSame s (kfromS c) d
  DeltaSFromR sh (DeltaFromS (STKR _ x) d) -> case ftkDelta d of
    y2 -> case sameSTK (ftkToSTK y2) (STKS sh x) of
      Just Refl -> evalRevSame s c d
      _ -> error "evalRevSame: different shapes in DeltaSFromR(DeltaFromS)"
  DeltaSFromR sh d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS sh $
      evalRevSame s (rfromS c) d
  DeltaSFromX sh (DeltaFromS (STKX _ x) d) -> case ftkDelta d of
    y2 -> case sameSTK (ftkToSTK y2) (STKS sh x) of
      Just Refl -> evalRevSame s c d
      _ -> error "evalRevSame: different shapes in DeltaSFromX(DeltaFromS)"
  DeltaSFromX sh d -> case ftkDelta d of
    FTKX sh2 x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS sh $
      withKnownShX (ssxFromShape sh2) $
      evalRevSame s (xfromS c) d

  DeltaXNestR sh1 SNat d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX sh1 $
      evalRevSame s (xunNestR c) d
  DeltaXNestS sh1 sh2 d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX sh1 $
      withKnownShS sh2 $
      evalRevSame s (xunNestS c) d
  DeltaXNest sh1 sh2 d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX sh1 $
      withKnownShX sh2 $
      evalRevSame s (xunNest c) d
  DeltaXUnNestR d -> case ftkDelta d of
    FTKX sh1 (FTKR sh2 x) | SNat <- shrRank sh2 ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (xnestR (ssxFromShape sh1) c) d
  DeltaXUnNestS d -> case ftkDelta d of
    FTKX sh1 (FTKS sh2 x) ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS sh2 $
      evalRevSame s (xnestS (ssxFromShape sh1) c) d
  DeltaXUnNest d -> case ftkDelta d of
    FTKX sh1 (FTKX sh2 x) ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX (ssxFromShape sh2) $
      evalRevSame s (xnest (ssxFromShape sh1) c) d

  d -> evalRev s c d
    -- the remaining constructors are already handled in evalRev, so let's use that

evalRevFromnMap :: forall target. (ADReadyNoLet target, ShareTensor target)
                => EvalState target -> EvalState target
evalRevFromnMap s@EvalState{nMap, dMap} =
  -- We discharge the non-vector cases before the vector ones, because
  -- the latter tend to create and store more cases and so enlarge
  -- the working set of cases.
  case DMap.maxViewWithKey nMap of
    Just (n :=> d, nMap2) ->
      let nstk = nodeIdToSTK n
          s2 = s {nMap = nMap2}
          errorMissing :: a
          errorMissing = error $ "evalRevFromnMap: missing cotangent " ++ show n
          s3 = case nstk of
            STKR @n _ (STKScalar @r) -> case DMap.lookup n dMap of
              Just (Cotangent c) -> evalRevRuntimeSpecialized @n @r s2 c d
              Nothing -> errorMissing
            STKS @sh _ (STKScalar @r) ->
              case DMap.lookup n dMap of
                Just (Cotangent c) -> evalSRuntimeSpecialized @sh @r s2 c d
                Nothing -> errorMissing
            STKX @sh _ (STKScalar @r) ->
              case DMap.lookup n dMap of
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
  :: forall target y. (ADReadyNoLet target, ShareTensor target)
  => IMap target -> ADMap target -> Delta target y
  -> (ADMap target, target (ADTensorKind y))
evalFwd params s d0 = case d0 of
  DeltaPair d1 d2 ->
    let (s2, t) = evalFwd params s d1
        (s3, u) = evalFwd params s2 d2
    in (s3, tpair t u)
  DeltaProject1 d ->
    let (s2, v) = evalFwd params s d
    in (s2, tproject1 v)
  DeltaProject2 d ->
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
  DeltaMapAccumR k bShs eShs q es df _rf acc0' es'
   | Refl <- lemBuildOfAD k (ftkToSTK bShs)
   , Refl <- lemBuildOfAD k (ftkToSTK eShs) ->
    let accShs = ftkDelta acc0'
        accShsAD = adFTK accShs
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
  DeltaMapAccumL k bShs eShs q es df _rf acc0' es'
   | Refl <- lemBuildOfAD k (ftkToSTK bShs)
   , Refl <- lemBuildOfAD k (ftkToSTK eShs) ->
    let accShs = ftkDelta acc0'
        accShsAD = adFTK accShs
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

  DeltaShare n d ->
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
  DeltaInput ftk inputId ->
    case DMap.lookup inputId params of
      Just dtk -> (s, toADTensorKindShared (ftkToSTK ftk)
                      $ evalTensorOrZero dtk)
      Nothing -> error "evalFwd: missing input"

  DeltaFromS stk (DeltaSFromR _ d)
    | y2 <- ftkDelta d
    , Just Refl <- sameSTK (adSTK stk) (adSTK $ ftkToSTK y2) ->
      evalFwd params s d
  DeltaFromS stk (DeltaSFromX _ d)
    | y2 <- ftkDelta d
    , Just Refl <- sameSTK (adSTK stk) (adSTK $ ftkToSTK y2) ->
      evalFwd params s d
  DeltaFromS stk d ->
    let stk2 = ftkToSTK $ ftkDelta d
    in second (tfromSShare (adSTK stk2) (adSTK stk)) $ evalFwd params s d

  _ -> case ftkDelta d0 of
    y -> case matchingFTK y (adFTK y) of
        Just Refl -> evalFwdSame params s d0
        _ -> (s, constantTarget 0 $ adFTK $ ftkDelta d0)

evalFwdSame
  :: forall target y.
     (ADReadyNoLet target, ShareTensor target, y ~ ADTensorKind y)
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
    case sameSTK (STKScalar @r1) (adSTK (STKScalar @r1)) of
      Just Refl -> second kcast $ evalFwdSame params s d
      _ -> (s, constantTarget 0 $ adFTK $ ftkDelta d0)

  d0@(DeltaCastR d) -> case ftkDelta d of
    y ->
      case sameSTK (ftkToSTK y) (adSTK (ftkToSTK y)) of
        Just Refl -> second rcast $ evalFwdSame params s d
        _ -> (s, constantTarget 0 $ adFTK $ ftkDelta d0)
  DeltaSum0R (DeltaZero (FTKR _ x)) -> (s, constantTarget 0 (FTKR ZSR x))
  DeltaSum0R d -> case ftkDelta d of
    FTKR sh x | SNat <- shrRank sh ->
      withKnownSTK (ftkToSTK x) $
      second rsum0 $ evalFwdSame params s d
  DeltaDot0R _ DeltaZero{} -> (s, rscalar 0)
  DeltaDot0R v d -> case ftkDelta d of
    FTKR sh x | SNat <- shrRank sh ->
      withKnownSTK (ftkToSTK x) $
      second (rdot0 v) $ evalFwdSame params s d
  DeltaIndexR SNat d ix -> case ftkDelta d of
    FTKR _ x | SNat <- ixrRank ix ->
      withKnownSTK (ftkToSTK x) $
      second (`rindex` ix) $ evalFwdSame params s d
  DeltaScatterR SNat SNat SNat sh d f -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      let (s2, t) = evalFwdSame params s d
      in (s2, rscatter sh t f)
  DeltaGatherR SNat SNat SNat sh d f -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      let (s2, t) = evalFwdSame params s d
      in (s2, rgather sh t f)
  DeltaAppendR d e -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      let (s2, t) = evalFwdSame params s d
          (s3, u) = evalFwdSame params s2 e
      in (s3, rappend t u)
  DeltaSliceR i n d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      second (rslice i n) $ evalFwdSame params s d
  DeltaReverseR d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      second rreverse $ evalFwdSame params s d
  DeltaTransposeR perm d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      second (rtranspose perm) $ evalFwdSame params s d
  DeltaReshapeR sh2 d -> case ftkDelta d of
    FTKR _sh x ->
      withKnownSTK (ftkToSTK x) $
      second (rreshape sh2) $ evalFwdSame params s d
  DeltaZipR d -> second rzip $ evalFwdSame params s d
  DeltaUnzipR d -> second runzip $ evalFwdSame params s d

  d0@(DeltaCastS d) -> case ftkDelta d of
    y ->
      case sameSTK (ftkToSTK y) (adSTK (ftkToSTK y)) of
        Just Refl -> second scast $ evalFwdSame params s d
        _ -> (s, constantTarget 0 $ adFTK $ ftkDelta d0)
  DeltaSum0S (DeltaZero (FTKS _ x)) -> (s, constantTarget 0 (FTKS ZSS x))
  DeltaSum0S d -> case ftkDelta d of
    FTKS sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS sh $
      second ssum0 $ evalFwdSame params s d
  DeltaDot0S _ DeltaZero{} -> (s, srepl 0)
  DeltaDot0S v d -> case ftkDelta d of
    FTKS sh FTKScalar ->
      withKnownShS sh $
      second (sdot0 v) $ evalFwdSame params s d
  DeltaIndexS shn d ix -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS shn $
      withKnownShS (ixsToShS ix) $
      second (`sindex` ix) $ evalFwdSame params s d
  DeltaScatterS @shm @shn shm shn shp d f -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS shm $
      withKnownShS shn $
      withKnownShS shp $
      let (s2, t) = evalFwdSame params s d
      in (s2, sscatter @_ @_ @shm @shn t f)
  DeltaGatherS @shm @shn shm shn shp d f -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS shm $
      withKnownShS shn $
      withKnownShS shp $
      let (s2, t) = evalFwdSame params s d
      in (s2, sgather @_ @_ @shm @shn t f)
  DeltaAppendS d e -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      let (s2, t) = evalFwdSame params s d
          (s3, u) = evalFwdSame params s2 e
      in (s3, sappend t u)
  DeltaSliceS i n k d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      second (sslice i n k) $ evalFwdSame params s d
  DeltaReverseS d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      second sreverse $ evalFwdSame params s d
  DeltaTransposeS perm d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      second (ttranspose perm) $ evalFwdSame params s d
  DeltaReshapeS sh2 d -> case ftkDelta d of
    FTKS _sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS sh2 $
      second sreshape $ evalFwdSame params s d
  DeltaZipS d -> second szip $ evalFwdSame params s d
  DeltaUnzipS d -> second sunzip $ evalFwdSame params s d

  d0@(DeltaCastX d) -> case ftkDelta d of
    y ->
      case sameSTK (ftkToSTK y) (adSTK (ftkToSTK y)) of
        Just Refl -> second xcast $ evalFwdSame params s d
        _ -> (s, constantTarget 0 $ adFTK $ ftkDelta d0)
  DeltaSum0X (DeltaZero (FTKX _ x)) -> (s, constantTarget 0 (FTKX ZSX x))
  DeltaSum0X d -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX (ssxFromShape sh) $
      second xsum0 $ evalFwdSame params s d
  DeltaDot0X _ DeltaZero{} -> (s, xrepl ZSX 0)
  DeltaDot0X v d -> case ftkDelta d of
    FTKX sh FTKScalar ->
      withKnownShX (ssxFromShape sh) $
      second (xdot0 v) $ evalFwdSame params s d
  DeltaIndexX @shm @shn shn d ix -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX shn $
-- TODO      withKnownShX (ixxToSSX ix) $
      withKnownShX (ssxTakeIx @shm @shn (ssxFromShape sh) ix) $
      second (`xindex` ix) $ evalFwdSame params s d
  DeltaScatterX @shm @shn shm shn shp sh d f -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX shm $
      withKnownShX shn $
      withKnownShX shp $
      let (s2, t) = evalFwdSame params s d
      in (s2, xscatter @_ @_ @shm @shn sh t f)
  DeltaGatherX @shm @shn shm shn shp sh d f -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX shm $
      withKnownShX shn $
      withKnownShX shp $
      let (s2, t) = evalFwdSame params s d
      in (s2, xgather @_ @_ @shm @shn sh t f)
  DeltaAppendX d e -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      let (s2, t) = evalFwdSame params s d
          (s3, u) = evalFwdSame params s2 e
      in (s3, xappend t u)
  DeltaSliceX i n k d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      second (xslice i n k) $ evalFwdSame params s d
  DeltaReverseX d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      second xreverse $ evalFwdSame params s d
  DeltaTransposeX @perm perm d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownPerm perm $
      second (xtranspose @_ @perm) $ evalFwdSame params s d
  DeltaReshapeX sh2 d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      second (xreshape sh2) $ evalFwdSame params s d
  DeltaZipX d -> second xzip $ evalFwdSame params s d
  DeltaUnzipX d -> second xunzip $ evalFwdSame params s d

  DeltaSFromK d -> let (s2, t) = evalFwdSame params s d
                   in (s2, sfromK t)
  DeltaSFromR sh (DeltaFromS (STKR _ x) d) -> case ftkDelta d of
    y2 -> case sameSTK (ftkToSTK y2) (STKS sh x) of
      Just Refl -> evalFwdSame params s d
      _ -> error "evalFwdSame: different shapes in DeltaSFromR(DeltaFromS)"
  DeltaSFromR sh d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS sh $
      second sfromR $ evalFwdSame params s d
  DeltaSFromX sh (DeltaFromS (STKX _ x) d) -> case ftkDelta d of
    y2 -> case sameSTK (ftkToSTK y2) (STKS sh x) of
      Just Refl -> evalFwdSame params s d
      _ -> error "evalFwdSame: different shapes in DeltaSFromX(DeltaFromS)"
  DeltaSFromX sh d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS sh $
      second sfromX $ evalFwdSame params s d

  DeltaXNestR sh1 SNat d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      second (xnestR sh1) $ evalFwdSame params s d
  DeltaXNestS sh1 sh2 d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS sh2 $
      second (xnestS sh1) $ evalFwdSame params s d
  DeltaXNest sh1 sh2 d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX sh2 $
      second (xnest sh1) $ evalFwdSame params s d
  DeltaXUnNestR d -> case ftkDelta d of
    FTKX sh1 (FTKR sh2 x) | SNat <- shrRank sh2 ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX (ssxFromShape sh1) $
      second xunNestR $ evalFwdSame params s d
  DeltaXUnNestS d -> case ftkDelta d of
    FTKX sh1 (FTKS sh2 x) ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX (ssxFromShape sh1) $
      withKnownShS sh2 $
      second xunNestS $ evalFwdSame params s d
  DeltaXUnNest d -> case ftkDelta d of
    FTKX sh1 (FTKX sh2 x) ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX (ssxFromShape sh1) $
      withKnownShX (ssxFromShape sh2) $
      second xunNest $ evalFwdSame params s d

  d -> evalFwd params s d
