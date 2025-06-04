{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Evaluation of delta expressions, that is, transpose of the linear
-- maps of which the delta expressions are sparse representations.
-- See comments in "HordeAd.Core.Delta".
module HordeAd.Core.DeltaEval
  ( -- * Delta expression evaluation
    gradientFromDelta, derivativeFromDelta
    -- * Exported to be specialized elsewhere
  , evalRev, evalRevFTK, evalRevSame, evalRevFromnMap, EvalState
  ) where

import Prelude

import Control.Arrow (second)
import Control.Exception.Assert.Sugar
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.Proxy (Proxy (Proxy))
import Data.Traversable (mapAccumL)
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Text.Show (showListWith)
import Text.Show.Functions ()
import Type.Reflection (typeRep)

import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation (permInverse)
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd.Core.CarriersADVal (unDeltaPairUnshared)
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Delta
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

-- * Top-level functions for computing derivatives from delta expressions

-- | The top-level function for computing a gradient of an objective function.
--
-- Delta expressions naturally denote forward derivatives, as encoded
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
-- of @f@, for which we compute the derivative, and @dt@ is a sensitivity
-- of the result of @f@, for which we compute the gradient.
-- Nota bene, this property is checked for many example objective functions
-- (and perturbations and sensitivities) in the horde-ad testsuite.
gradientFromDelta
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => FullShapeTK x
  -> FullShapeTK z
  -> target (ADTensorKind z)
  -> Delta target z
  -> target (ADTensorKind x)
gradientFromDelta !xftk !zftk !dt deltaTopLevel =
  let s0 = initEvalState xftk
      s1 = evalRev zftk s0 dt deltaTopLevel
      s2 = evalRevFromnMap s1
      (res, remainder) =
        rebuildInputs @(ADTensorKind x) (DMap.toAscList $ iMap s2) s2
        $ adFTK xftk
  in assert (null remainder) res

-- | The top-level function for computing a (forward) derivative
-- of an objective function.
derivativeFromDelta
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => Delta target z -> FullShapeTK (ADTensorKind x)
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
          withKnownSTK (ftkToSTK $ inputIdToFTK k) $
          showsPrec 2 k . showString " :=> " . showsPrec 1 target)
        (DMap.toList demap)

show_IMap
  :: (forall y. KnownSTK y => Show (TensorOrZero target y))
  => IMap target -> String
show_IMap iMap = showsPrec_IMap 0 iMap ""

type role Cotangent nominal nominal
newtype Cotangent target y =
  Cotangent {unCotangent :: target (ADTensorKind y)}

-- | This is a tensor representation where zero tensors are marked specially
-- at construction, when it's cheap to do so (as opposed to, later on.
-- requiring a traversal of large terms or checking that each cell
-- of a huge concrete array is zero). It also makes the computation
-- of a special case of addTensorOrZero cheaper.
type role TensorOrZero nominal nominal
data TensorOrZero target y =
    TOTensor (target y)
  | TOZero (FullShapeTK y)
  deriving Show

evalTensorOrZero :: forall target x. ADReadyNoLet target
                 => TensorOrZero target x -> target x
evalTensorOrZero = \case
  TOTensor t -> t
  TOZero ftk -> tdefTarget ftk

-- The ShareTensor constraint is needed, despite what GHC says,
-- in order not to require duplicable arguments.
addTensorOrZero :: forall target y. (ADReadyNoLet target, ShareTensor target)
                => SingletonTK y
                -> TensorOrZero target y -> TensorOrZero target y
                -> TensorOrZero target y
addTensorOrZero stk a b = case (a, b) of
  (TOTensor ta, TOTensor tb) -> TOTensor $ taddTarget stk ta tb
    -- target has a ShareTensor instance, so ta and tb don't need
    -- to be duplicable
  (TOZero{}, _) -> b
  (_, TOZero{}) -> a

-- Matches generateDSumsDummy.
rebuildInputs :: forall ady target. ADReadyNoLet target
              => [DSum (InputId target) (TensorOrZero target)]
              -> EvalState target  -- original state; only for error messages
              -> FullShapeTK ady
              -> (target ady, [DSum (InputId target) (TensorOrZero target)])
rebuildInputs els s2 ftk = case ftk of
  FTKProduct ftk1 ftk2 ->
      let (t1, rest1) = rebuildInputs els s2 ftk1
          (t2, rest2) = rebuildInputs rest1 s2 ftk2
          !t = tpair t1 t2
      in (t, rest2)
  _ | differentiableFTK ftk -> case els of
    (n :=> tz@(TOTensor t)) : rest ->
      case matchingFTK (inputIdToFTK n) ftk of
        Just Refl ->
          (t, rest)
        _ | Dict <- lemKnownSTK (ftkToSTK $ inputIdToFTK n) ->
          error $ "rebuildInputs: wrong Tensor type: "
                  ++ show (n, tz, show_IMap (iMap s2))
    (n :=> tz@(TOZero ftk2)) : rest ->
      case matchingFTK ftk2 ftk of
        Just Refl ->
          let !zero = tdefTarget ftk
          in (zero, rest)
          -- TODO: actually pass this ZERO through to optimizers
          -- and use there to avoid updating the gradient
          -- and maybe use elsewhere, too, to manage sparsity a bit.
          -- We'd probably need TKProduct to take TensorOrZero.
        _ | Dict <- lemKnownSTK (ftkToSTK $ inputIdToFTK n) ->
          error $ "rebuildInputs: wrong Zero type: "
                  ++ show (n, tz, show_IMap (iMap s2))
    _ -> error $ "rebuildInputs: illegal TensorOrZero: "
                 ++ show_IMap (iMap s2)
  _ -> (tdefTarget ftk, els)

-- Matches generateDeltaInputs.
generateDSumsDummy :: Int -> FullShapeTK y
                   -> ([DSum (InputId target) (TensorOrZero target)], Int)
generateDSumsDummy j ftk  = case ftk of
  FTKProduct ftk1 ftk2 ->
    let (ds1, j1) = generateDSumsDummy j ftk1
        (ds2, j2) = generateDSumsDummy j1 ftk2
    in (ds1 ++ ds2, j2)
  _ | differentiableFTK ftk -> ([mkInputId ftk j :=> TOZero ftk], j + 1)
  _ -> ([], j)

-- Matches generateDeltaInputs.
generateDSums :: ShareTensor target
              => Int -> FullShapeTK y -> target y
              -> ([DSum (InputId target) (TensorOrZero target)], Int)
generateDSums j ftk t = case ftk of
  FTKProduct ftk1 ftk2 ->
    let (t1, t2) = tunpair t
        (ds1, j1) = generateDSums j ftk1 t1
        (ds2, j2) = generateDSums j1 ftk2 t2
    in (ds1 ++ ds2, j2)
  _ | differentiableFTK ftk -> ([mkInputId ftk j :=> TOTensor t], j + 1)
  _ -> ([], j)


-- * Delta evaluation state

-- | The state of evaluation. It consists of several maps.
-- The maps indexed by input identifiers and node identifiers
-- eventually store cotangents for their respective nodes.
-- The cotangents are built gradually during the evaluation,
-- by summing cotangent contributions.
--
-- Data invariant: keys nMap == keys dMap.
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
      -- and/or not take into account the whole summed context when finally
      -- evaluating
  }

-- | Initialization of the evalutation state, which consists of
-- creating the finite maps that hold values associated with inputs
-- and with (possibly shared) term tree nodes.
-- The former are usually initialized with dummy values so that it's cheap
-- to check if any update has already been performed to a cell
-- (allocating big vectors filled with zeros is too costly,
-- especially if never used in an iteration, and adding to such vectors
-- and especially using them as cotangent accumulators is wasteful).
initEvalState :: FullShapeTK x -> EvalState target
initEvalState ftk0 =
  let iMap = DMap.fromDistinctAscList $ fst $ generateDSumsDummy 0 $ adFTK ftk0
      dMap = DMap.empty
      nMap = DMap.empty
  in EvalState {..}


-- * Reverse pass, transpose/evaluation of the delta expressions

evalRevScalarRuntimeSpecialized
  :: forall r target.
     (GoodScalar r, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind (TKScalar r))
  -> Delta target (TKScalar r)
  -> EvalState target
{-# INLINE evalRevScalarRuntimeSpecialized #-}
evalRevScalarRuntimeSpecialized !s !c =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalRevSame @(TKScalar Double) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalRevSame @(TKScalar Float) s c
      _ -> const s

evalRevRRuntimeSpecialized
  :: forall n r target.
     (GoodScalar r, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind (TKR n r))
  -> Delta target (TKR n r)
  -> EvalState target
{-# INLINE evalRevRRuntimeSpecialized #-}
evalRevRRuntimeSpecialized !s !c =
  -- We dispatch on all expected underyling scalar types, which is
  -- necessary to run the correct specialization when unpacking
  -- an existential type. All IfDifferentiable instances should
  -- be included in the list of expected underlying scalar types.
  -- If the scalar type is not on the list, performance suffers greatly.
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
{-# INLINE evalSRuntimeSpecialized #-}
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
{-# INLINE evalXRuntimeSpecialized #-}
evalXRuntimeSpecialized !s !c =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalRevSame @(TKX sh Double) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalRevSame @(TKX sh Float) s c
      _ -> const s

-- | Reverse pass, that is, transpose/evaluation of the delta expressions
-- in order to produce the gradient for the objective function runtime
-- trace represented by the delta expression.
--
-- The first argument is the tensor kind that constrains the shapes
-- of the contangent accumulator and the delta expression arguments.
-- The second is the evaluation state being modified.
-- The third is the cotangent accumulator that will become an actual
-- cotangent contribution when complete (see below for an explanation).
-- The fourth is the delta expression node to evaluate.
--
-- Obtaining the gradient amounts to transposing the linear map
-- that is straightforwardly represented by the delta expression.
-- The @evalRev@ function transposes the linear map and,
-- at the same time, evaluates the transposed map on the cotangent accumulator
-- value contained in the third argument. If the cotangent and the tensor
-- operations are symbolic, the resulting value represents the transposed
-- map itself, if its free variables are treated as the map's inputs.
evalRev
  :: forall y target.
     (ADReadyNoLet target, ShareTensor target)
  => FullShapeTK y
  -> EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalRev ftk !s !c d = case ftk of
  FTKScalar @r -> evalRevScalarRuntimeSpecialized @r s c d
  FTKR @n _ (FTKScalar @r) -> evalRevRRuntimeSpecialized @n @r s c d
  FTKS @sh _ (FTKScalar @r) -> evalSRuntimeSpecialized @sh @r s c d
  FTKX @sh _ (FTKScalar @r) -> evalXRuntimeSpecialized @sh @r s c d
  _ -> evalRevFTK s c d

-- | A helper function to `evalRev`. The @FTK@ suffix denotes it doesn't get
-- an FTK as an argument but reconstructs it as needed.
--
-- All constructors that can have a type with TKProduct kind
-- need to be handled here,
-- as opposed to in 'evalRevSame', except for DeltaInput that is always
-- constructed only in basic kinds even though its type permits others.
evalRevFTK
  :: forall y target.
     (ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalRevFTK !s !c d0 = case d0 of
  DeltaShare n d ->
    -- In this context, by construction, @d@ is the dual component
    -- of a dual number term. Let's say that, at this point, evaluation
    -- considers position (node) p out of possibly multiple positions
    -- at which that dual number resides in the whole term tree
    -- of the dual number representation of the objective function.
    -- (Equivalently, considers edge p, one of many leading to the only
    -- node with identifier @n@ in the DAG representing the term).
    -- If so, the @c@ argument of @eval0@ is the cotangent
    -- contribution for position p, that is, the partial derivative
    -- of the objective function with respect to position p.
    --
    -- If there are indeed multiple such positions
    -- (the term is non-trivially shared) then,
    -- over the course of evaluation, cotangent contributions
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
    assert (case d of  -- should match shareDelta
              DeltaZero{} -> False
              DeltaPair{} -> False
              DeltaInput{} -> False
              DeltaShare{} -> False
              _ -> True)
    $ if DMap.member n $ nMap s
      then let addc x =
                 Cotangent $ taddTarget (adSTK $ ftkToSTK $ nodeIdToFTK n)
                                        c (unCotangent x)
             -- target has a ShareTensor instance, so taddTarget arguments
             -- don't need to be duplicable
           in s {dMap = DMap.adjust addc n $ dMap s}
      else let cd = Cotangent c
           in s { nMap = DMap.insert n d $ nMap s
                , dMap = DMap.insert n cd $ dMap s }

  DeltaPair d1 d2 ->
    let (c1, c2) = tunpair c
    in evalRevFTK (evalRevFTK s c1 d1) c2 d2
  DeltaProject1 d -> case ftkDelta d of
    FTKProduct _ ftk2 ->
      let zero = tdefTarget $ adFTK ftk2
      in evalRevFTK s (tpair c zero) d
    -- if y is, e.g., TKR 0 Int64, we eval this delta anyway, even though
    -- we could ignore it at the price of complicating or duplicating
    -- the code slightly more
  DeltaProject2 d -> case ftkDelta d of
    FTKProduct ftk1 _ ->
      let zero = tdefTarget $ adFTK ftk1
      in evalRevFTK s (tpair zero c) d
  DeltaFromVector snat stk ld | Refl <- lemBuildOfAD snat stk ->
    let cxs = tunravelToListShare snat (adSTK stk) c
    in foldl' (\ !s2 (cx, d2) -> evalRevFTK s2 cx d2) s
       $ zip cxs (V.toList ld)
  DeltaSum snat stk d | Refl <- lemBuildOfAD snat stk ->
    evalRevFTK s (treplicate snat (adSTK stk) c) d
  DeltaReplicate snat stk d | Refl <- lemBuildOfAD snat stk ->
    evalRevFTK s (tsum snat (adSTK stk) c) d
  DeltaMapAccumR k bftk eftk q es _df rf acc0' es'
   | Refl <- lemBuildOfAD k (ftkToSTK bftk)
   , Refl <- lemBuildOfAD k (ftkToSTK eftk) ->
    let accftk = ftkDelta acc0'
        accftkAD = adFTK accftk
        bftkAD = adFTK bftk
        eftkAD = adFTK eftk
        (c0, crest) = tunpair c
        dacc_des =
          tmapAccumL (Proxy @target)
                     k accftkAD eftkAD (FTKProduct bftkAD
                                                   (FTKProduct accftk eftk))
                     (\dx db_acc_e ->
                        ttlet db_acc_e $ \ !db_acc_e1 ->
                          unHFun rf (tpair (tpair dx (tproject1 db_acc_e1))
                                           (tproject2 db_acc_e1)))
                     c0
                     (tpair crest (tpair q es))
        (dacc, des) = tunpair dacc_des
        s2 = evalRevFTK s dacc acc0'
    in evalRevFTK s2 des es'
  DeltaMapAccumL k bftk eftk q es _df rf acc0' es'
   | Refl <- lemBuildOfAD k (ftkToSTK bftk)
   , Refl <- lemBuildOfAD k (ftkToSTK eftk) ->
    let accftk = ftkDelta acc0'
        accftkAD = adFTK accftk
        bftkAD = adFTK bftk
        eftkAD = adFTK eftk
        (c0, crest) = tunpair c
        dacc_des =
          tmapAccumR (Proxy @target)
                     k accftkAD eftkAD (FTKProduct bftkAD
                                                   (FTKProduct accftk eftk))
                     (\dx db_acc_e ->
                        ttlet db_acc_e $ \ !db_acc_e1 ->
                          unHFun rf (tpair (tpair dx (tproject1 db_acc_e1))
                                           (tproject2 db_acc_e1)))
                     c0
                     (tpair crest (tpair q es))
        (dacc, des) = tunpair dacc_des
        s2 = evalRevFTK s dacc acc0'
    in evalRevFTK s2 des es'

  DeltaFromS stk (DeltaSFromR _ d)
    | y2 <- ftkDelta d
    , Just Refl <- sameSTK (adSTK stk) (adSTK $ ftkToSTK y2) ->
      evalRev y2 s c d
  DeltaFromS stk (DeltaSFromX _ d)
    | y2 <- ftkDelta d
    , Just Refl <- sameSTK (adSTK stk) (adSTK $ ftkToSTK y2) ->
      evalRev y2 s c d
  DeltaFromS stk d
    | y2 <- ftkDelta d -> case (ftkToSTK y2, stk) of
    (stky, stkz) | Just Refl <- sameSTK stky stkz -> evalRev y2 s c d
    (STKS ZSS yx@(STKScalar @ry), STKScalar @rz) ->
      case testEquality (typeRep @ry) (typeRep @rz) of
        Just Refl -> case sameSTK yx (adSTK yx) of
          Just Refl -> evalRev y2 s (sfromK c) d
          _ -> s
        Nothing -> error "evalRev: tensor kinds don't match"
    (STKS shy yx, STKR nx zx) | Dict <- lemKnownSTKOfAD yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) nx) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          evalRev y2 s (sfromR c) d
        _ -> error "evalRev: tensor kinds don't match"
    (STKS shy yx, STKX shx zx) | Dict <- lemKnownSTKOfAD yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) (ssxRank shx)) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          evalRev y2 s (sfromX c) d
        _ -> error "evalRev: tensor kinds don't match"
    (STKProduct{}, STKProduct stkz1 stkz2) ->
        let (c1, c2) = tunpair c
            (d1, d2) = unDeltaPairUnshared d
        in evalRevFTK (evalRevFTK s c1 (DeltaFromS stkz1 d1))
                      c2 (DeltaFromS stkz2 d2)
             -- TODO: make this compositional and evaluate d only once
    _ -> error "evalRev: wrong tensor kinds"

  _ -> let y = ftkDelta d0
       in case matchingFTK y (adFTK y) of
         Just Refl -> evalRevSame s c d0
         _ -> s  -- the constructors remaining here have y that is
                 -- a non-TKProduct so if y is equal to ADTensorKind y,
                 -- the latter has the Z0 scalar type and so no influence
                 -- on the derivative.

-- | A helper function to `evalRev`. It assumes the scalar underlying
-- the tensor kind of its arguments is differentiable.
--
-- All constructors that can only have types with non-TKProduct kinds
-- (and the DeltaInput constructor and the vector space constructors)
-- can be handled here, where the extra equality constraint makes it easier.
evalRevSame
  :: forall y target.
     (ADReadyNoLet target, ShareTensor target, y ~ ADTensorKind y)
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalRevSame !s !c = \case
  DeltaInput i ->
    let cs = TOTensor c
    in s {iMap = DMap.adjust (addTensorOrZero (ftkToSTK $ inputIdToFTK i) cs) i
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
  DeltaScale (NestedTarget k) d -> evalRevSame s (k * c) d
  DeltaAdd d e ->
    let cShared = tshare c
    in evalRevSame (evalRevSame s cShared d) cShared e

  DeltaCastK @r1 d ->
    evalRevScalarRuntimeSpecialized
    s (toADTensorKindShared (FTKScalar @r1) $ tkcast c) d
  DeltaCastR d -> case ftkDelta d of
    y ->
      evalRevRRuntimeSpecialized
      s (toADTensorKindShared y $ trcast c) d
  DeltaSum0R d -> case ftkDelta d of
    FTKR sh x | SNat <- shrRank sh ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (trreplicate0N sh c) d
  DeltaDot0R v d -> case ftkDelta d of
    FTKR sh x | SNat <- shrRank sh ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (v * trreplicate0N (rshape v) c) d
        -- too slow: evalRevSame s (rmap0N (* (tscalar c)) v) vd
  DeltaIndexR SNat d ix -> case ftkDelta d of
    FTKR sh x | SNat <- ixrRank ix ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (troneHot (takeShape sh) c ix) d  -- TODO: ixrToShR ix
  DeltaScatterR SNat SNat SNat _sh d f -> case ftkDelta d of
    FTKR sh x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (trgather sh c f) d
  DeltaGatherR SNat SNat SNat _sh d f -> case ftkDelta d of
    FTKR sh x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (trscatter sh c f) d
  DeltaAppendR d e -> case (ftkDelta d, ftkDelta e) of
    (FTKR (m :$: _) x, FTKR (n :$: _) _) ->
      withKnownSTK (ftkToSTK x) $
      let cShared = tshare c
          s2 = evalRevSame s (trslice 0 m cShared) d
      in evalRevSame s2 (trslice m n cShared) e
    _ -> error "evalRevSame: impossible pattern needlessly required"
  DeltaSliceR i n d -> case ftkDelta d of
    FTKR (l :$: rest) x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (trappend
                       (tdefTarget (FTKR (i :$: rest) x))
                       (trappend c
                          (tdefTarget (FTKR (l - i - n :$: rest) x)))) d
    FTKR ZSR _ -> error "evalRevSame: impossible pattern needlessly required"
  DeltaReverseR d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (trreverse c) d
  DeltaTransposeR perm d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      let permR = permRInverse perm
      in evalRevSame s (trtranspose permR c) d
  DeltaReshapeR _sh2 d -> case ftkDelta d of
    FTKR sh x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (trreshape sh c) d
  DeltaZipR d -> evalRevSame s (runzip c) d
  DeltaUnzipR d -> case ftkDelta d of
    FTKR _ (FTKProduct y z) ->
      withKnownSTK (ftkToSTK y) $
      withKnownSTK (ftkToSTK z) $
      evalRevSame s (rzip c) d

  DeltaCastS d -> case ftkDelta d of
    y ->
      evalSRuntimeSpecialized
      s (toADTensorKindShared y $ tscast c) d
  DeltaSum0S d -> case ftkDelta d of
    FTKS sh x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (tsreplicate0N sh c) d
  DeltaDot0S v d -> case ftkDelta d of
    FTKS sh FTKScalar ->
      evalRevSame s (v * tsreplicate0N sh c) d
  DeltaIndexS shn d ix -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS shn $
      withKnownShS (ixsToShS ix) $
      evalRevSame s (tsoneHot c ix) d
  DeltaScatterS @shm @shn shm shn shp d f -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS shm $
      withKnownShS shn $
      withKnownShS shp $
      evalRevSame s (tsgather @_ @shm @shn c f) d
  DeltaGatherS @shm @shn shm shn shp d f -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS shm $
      withKnownShS shn $
      withKnownShS shp $
      evalRevSame s (tsscatter @_ @shm @shn c f) d
  DeltaAppendS d e -> case (ftkDelta d, ftkDelta e) of
    (FTKS (msnat :$$ _) x, FTKS (_ :$$ _) _) ->
      withKnownSTK (ftkToSTK x) $
      let cShared = tshare c
          s2 = evalRevSame s (tsslice (SNat @0) SNat SNat cShared) d
      in evalRevSame s2 (tsslice msnat SNat SNat cShared) e
  DeltaSliceS i@SNat _ k@SNat d -> case ftkDelta d of
    FTKS (_ :$$ sh) x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (tsappend
                       (tdefTarget (FTKS (i :$$ sh) x))
                          (tsappend
                             c (tdefTarget (FTKS (k :$$ sh) x)))) d
  DeltaReverseS d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (tsreverse c) d
  DeltaTransposeS @perm @sh2 perm d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      permInverse perm $ \(permRev :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix
                        permR (Permutation.PermutePrefix perm sh2) :~: sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank (Permutation.PermutePrefix perm sh2) :~: Rank sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank permR :~: Rank perm)
        $ evalRevSame s (tstranspose permRev c) d
  DeltaReshapeS _sh2 d -> case ftkDelta d of
    FTKS sh x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (tsreshape sh c) d
  DeltaZipS d -> evalRevSame s (sunzip c) d
  DeltaUnzipS d -> case ftkDelta d of
    FTKS _ (FTKProduct y z) ->
      withKnownSTK (ftkToSTK y) $
      withKnownSTK (ftkToSTK z) $
      evalRevSame s (szip c) d

  DeltaCastX d -> case ftkDelta d of
    y ->
      evalXRuntimeSpecialized
      s (toADTensorKindShared y $ txcast c) d
  DeltaSum0X d -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX (ssxFromShX sh) $
      evalRevSame s (txreplicate0N sh c) d
  DeltaDot0X v d -> case ftkDelta d of
    FTKX sh FTKScalar ->
      withKnownShX (ssxFromShX sh) $
      evalRevSame s (v * txreplicate0N (xshape v) c) d
  DeltaIndexX @shm @shn shn d ix -> case ftkDelta d of
    FTKX sh x | SNat @len <- ixxRank ix ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX shn $
      withKnownShX (ssxFromShX sh) $
      withKnownShX (ssxTakeIx @shm @shn (ssxFromShX sh) ix) $
      gcastWith (unsafeCoerceRefl :: Take (Rank shm) (shm ++ shn) :~: shm) $
      evalRevSame s (txoneHot (takeShX @len sh) c ix) d
--TODO      evalRevSame s (xoneHot (shxTakeSSX (Proxy @shn) sh
--                                         (ixxToSSX ix)) c ix) d
  DeltaScatterX @shm @shn shm shn shp _sh d f -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX shm $
      withKnownShX shn $
      withKnownShX shp $
      evalRevSame s (txgather @_ @shm @shn sh c f) d
  DeltaGatherX @shm @shn shm shn shp _sh d f -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX shm $
      withKnownShX shn $
      withKnownShX shp $
      evalRevSame s (txscatter @_ @shm @shn sh c f) d
  DeltaAppendX d e -> case (ftkDelta d, ftkDelta e) of
    (FTKX (Nested.SKnown m@SNat :$% _) x, FTKX (Nested.SKnown SNat :$% _) _) ->
      withKnownSTK (ftkToSTK x) $
      let cShared = tshare c
          s2 = evalRevSame s (txslice (SNat @0) SNat SNat cShared) d
      in evalRevSame s2 (txslice m SNat SNat cShared) e
  DeltaSliceX i@SNat _ k@SNat d -> case ftkDelta d of
    FTKX (_ :$% sh) x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (txappend
                       (tdefTarget (FTKX (Nested.SKnown i :$% sh) x))
                          (txappend
                             c (tdefTarget
                                  (FTKX (Nested.SKnown k :$% sh) x)))) d
  DeltaReverseX d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (txreverse c) d
  DeltaTransposeX @perm @sh2 perm d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      permInverse perm $ \(permR :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix
                        permR (Permutation.PermutePrefix perm sh2) :~: sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Rank (Permutation.PermutePrefix perm sh2) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Rank permR :~: Rank perm) $
        evalRevSame s (txtranspose permR c) d
  DeltaReshapeX _sh2 d -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (ftkToSTK x) $
      evalRevSame s (txreshape sh c) d
  DeltaZipX d -> evalRevSame s (xunzip c) d
  DeltaUnzipX d -> case ftkDelta d of
    FTKX _ (FTKProduct y z) ->
      withKnownSTK (ftkToSTK y) $
      withKnownSTK (ftkToSTK z) $
      evalRevSame s (xzip c) d

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
      withKnownShX (ssxFromShX sh2) $
      evalRevSame s (xfromS c) d
  DeltaCastCastable @a c1 astk bftk d -> case ftkDelta d of
    aftk ->
      -- This is implied by the form of c1.
      gcastWith (unsafeCoerceRefl :: ADTensorKind a :~: a) $
      evalRevSame
        s (tcastCastable (transposeTKCastable astk c1) (ftkToSTK bftk) aftk c) d

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
      evalRevSame s (xnestR (ssxFromShX sh1) c) d
  DeltaXUnNestS d -> case ftkDelta d of
    FTKX sh1 (FTKS sh2 x) ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS sh2 $
      evalRevSame s (xnestS (ssxFromShX sh1) c) d
  DeltaXUnNest d -> case ftkDelta d of
    FTKX sh1 (FTKX sh2 x) ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX (ssxFromShX sh2) $
      evalRevSame s (xnest (ssxFromShX sh1) c) d

  d -> evalRevFTK s c d
    -- the remaining constructors are already handled in evalRevFTK

transposeTKCastable :: SingletonTK a -> TKCastable a b -> TKCastable b a
transposeTKCastable astk c0 = case c0 of
  CastId -> CastId
  CastCmp c1 c2 -> CastCmp (transposeTKCastable astk c2)
                           (transposeTKCastable (castSTK c2 astk) c1)
  CastRX | STKR @n _ x <- astk
         , Refl <- lemRankReplicate (Proxy @n) ->
    CastXR x
  CastSX -> CastXS
  CastXR @_ @sh _stk | Refl <- lemRankReplicate (Proxy @(Rank sh)) ->
    CastCmp (CastXX' astk) CastRX
  CastXS -> CastSX
  CastXS' (STKS sh _) | Refl <- lemRankMapJust sh ->
    CastCmp (CastXX' astk) CastSX
  CastXX' _stk -> CastXX' astk
  CastRR c | STKR _ x <- astk -> CastRR (transposeTKCastable x c)
  CastSS c | STKS _ x <- astk -> CastSS (transposeTKCastable x c)
  CastXX c | STKX _ x <- astk -> CastXX (transposeTKCastable x c)
  CastT2 c1 c2 | STKProduct x1 x2 <- astk ->
    CastT2 (transposeTKCastable x1 c1) (transposeTKCastable x2 c2)
  Cast0X _stk -> CastX0
  CastX0 | STKX ZKX x <- astk -> Cast0X x
  CastNest _stk -> CastUnnest
  CastUnnest | (STKX sh (STKX _ x)) <- astk -> CastNest (STKX sh x)
  CastZip stk1 stk2 -> CastUnzip stk1 stk2
  CastUnzip stk1 stk2 -> CastZip stk1 stk2

evalRevFromnMap :: forall target. (ADReadyNoLet target, ShareTensor target)
                => EvalState target -> EvalState target
evalRevFromnMap s@EvalState{nMap, dMap} =
  case DMap.maxViewWithKey nMap of
    Just (n :=> d, nMap2) ->
      let s2 = s {nMap = nMap2}
          s3 = case DMap.lookup n dMap of
            Just (Cotangent c) -> evalRev (nodeIdToFTK n) s2 c d
            Nothing -> error $ "evalRevFromnMap: missing cotangent " ++ show n
      in evalRevFromnMap s3
    Nothing -> s  -- loop ends

{- TODO: optimize similarly?
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
-- to compute it's dual number result) and along the direction vector
-- given by the parameters in the arguments.
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
  DeltaInput inputId ->
    case DMap.lookup inputId params of
      Just dtk -> (s, toADTensorKindShared (inputIdToFTK inputId)
                      $ evalTensorOrZero dtk)
      Nothing -> error "evalFwd: missing input"

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
    in (s2, tfromVector snat (adSTK stk) l)
  DeltaSum snat stk d | Refl <- lemBuildOfAD snat stk ->
    let (s2, t) = evalFwd params s d
    in (s2, tsum snat (adSTK stk) t)
  DeltaReplicate snat stk d | Refl <- lemBuildOfAD snat stk ->
    let (s2, t) = evalFwd params s d
    in (s2, treplicate snat (adSTK stk) t)
  DeltaMapAccumR k bftk eftk q es df _rf acc0' es'
   | Refl <- lemBuildOfAD k (ftkToSTK bftk)
   , Refl <- lemBuildOfAD k (ftkToSTK eftk) ->
    let accftk = ftkDelta acc0'
        accftkAD = adFTK accftk
        bftkAD = adFTK bftk
        eftkAD = adFTK eftk
        (s2, cacc0) = evalFwd params s acc0'
        (s3, ces) = evalFwd params s2 es'
    in (s3, tmapAccumR (Proxy @target)
                       k accftkAD bftkAD (FTKProduct eftkAD
                                                     (FTKProduct accftk eftk))
                       (\dacc de_acc_e ->
                        ttlet de_acc_e $ \ !de_acc_e1 ->
                          unHFun df (tpair (tpair dacc (tproject1 de_acc_e1))
                                           (tproject2 de_acc_e1)))
                       cacc0
                       (tpair ces (tpair q es)))
  DeltaMapAccumL k bftk eftk q es df _rf acc0' es'
   | Refl <- lemBuildOfAD k (ftkToSTK bftk)
   , Refl <- lemBuildOfAD k (ftkToSTK eftk) ->
    let accftk = ftkDelta acc0'
        accftkAD = adFTK accftk
        bftkAD = adFTK bftk
        eftkAD = adFTK eftk
        (s2, cacc0) = evalFwd params s acc0'
        (s3, ces) = evalFwd params s2 es'
    in (s3, tmapAccumL (Proxy @target)
                       k accftkAD bftkAD (FTKProduct eftkAD
                                                     (FTKProduct accftk eftk))
                       (\dacc de_acc_e ->
                        ttlet de_acc_e $ \ !de_acc_e1 ->
                          unHFun df (tpair (tpair dacc (tproject1 de_acc_e1))
                                           (tproject2 de_acc_e1)))
                       cacc0
                       (tpair ces (tpair q es)))

  DeltaFromS stk (DeltaSFromR _ d)
    | y2 <- ftkDelta d
    , Just Refl <- sameSTK (adSTK stk) (adSTK $ ftkToSTK y2) ->
      evalFwd params s d
  DeltaFromS stk (DeltaSFromX _ d)
    | y2 <- ftkDelta d
    , Just Refl <- sameSTK (adSTK stk) (adSTK $ ftkToSTK y2) ->
      evalFwd params s d
  DeltaFromS stk d ->
    withKnownSTK (adSTK $ ftkToSTK $ ftkDelta d) $
    second (tfromS (adSTK stk)) $ evalFwd params s d

  _ -> let y = ftkDelta d0
           ay = adFTK y
       in case matchingFTK y ay of
         Just Refl -> evalFwdSame params s d0
         _ -> (s, tdefTarget ay)

evalFwdSame
  :: forall target y.
     (ADReadyNoLet target, ShareTensor target, y ~ ADTensorKind y)
  => IMap target -> ADMap target -> Delta target y
  -> (ADMap target, target (ADTensorKind y))
evalFwdSame params s = \case
  DeltaInput inputId ->
    case DMap.lookup inputId params of
      Just dtk -> (s, evalTensorOrZero dtk)
      Nothing -> error "evalFwdSame: missing input"

  -- See the comment about these three in evalRevSame.
  DeltaZero ftk -> (s, tdefTarget $ adFTK ftk)
  DeltaScale (NestedTarget k) d -> second (* k) $ evalFwdSame params s d
  DeltaAdd d e -> let (s2, t) = evalFwdSame params s d
                      (s3, u) = evalFwdSame params s2 e
                  in (s3, t + u)

  d0@(DeltaCastK @r1 d) ->
    case sameSTK (STKScalar @r1) (adSTK (STKScalar @r1)) of
      Just Refl -> second tkcast $ evalFwdSame params s d
      _ -> (s, tdefTarget $ adFTK $ ftkDelta d0)

  d0@(DeltaCastR d) -> case ftkDelta d of
    y ->
      case sameSTK (ftkToSTK y) (adSTK (ftkToSTK y)) of
        Just Refl -> second trcast $ evalFwdSame params s d
        _ -> (s, tdefTarget $ adFTK $ ftkDelta d0)
  DeltaSum0R (DeltaZero (FTKR _ x)) -> (s, tdefTarget (FTKR ZSR x))
  DeltaSum0R d -> case ftkDelta d of
    FTKR sh x | SNat <- shrRank sh ->
      withKnownSTK (ftkToSTK x) $
      second trsum0 $ evalFwdSame params s d
  DeltaDot0R _ DeltaZero{} -> (s, trconcrete $ Nested.rscalar 0)
  DeltaDot0R v d -> case ftkDelta d of
    FTKR sh x | SNat <- shrRank sh ->
      withKnownSTK (ftkToSTK x) $
      second (trdot0 v) $ evalFwdSame params s d
  DeltaIndexR SNat d ix -> case ftkDelta d of
    FTKR _ x | SNat <- ixrRank ix ->
      withKnownSTK (ftkToSTK x) $
      second (`trindex` ix) $ evalFwdSame params s d
  DeltaScatterR SNat SNat SNat sh d f -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      let (s2, t) = evalFwdSame params s d
      in (s2, trscatter sh t f)
  DeltaGatherR SNat SNat SNat sh d f -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      let (s2, t) = evalFwdSame params s d
      in (s2, trgather sh t f)
  DeltaAppendR d e -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      let (s2, t) = evalFwdSame params s d
          (s3, u) = evalFwdSame params s2 e
      in (s3, trappend t u)
  DeltaSliceR i n d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      second (trslice i n) $ evalFwdSame params s d
  DeltaReverseR d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      second trreverse $ evalFwdSame params s d
  DeltaTransposeR perm d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (ftkToSTK x) $
      second (trtranspose perm) $ evalFwdSame params s d
  DeltaReshapeR sh2 d -> case ftkDelta d of
    FTKR _sh x ->
      withKnownSTK (ftkToSTK x) $
      second (trreshape sh2) $ evalFwdSame params s d
  DeltaZipR d -> case ftkDelta d of
    FTKProduct (FTKR _ y) (FTKR _ z) ->
      withKnownSTK (ftkToSTK y) $
      withKnownSTK (ftkToSTK z) $ second rzip $ evalFwdSame params s d
  DeltaUnzipR d -> second runzip $ evalFwdSame params s d

  d0@(DeltaCastS d) -> case ftkDelta d of
    y ->
      case sameSTK (ftkToSTK y) (adSTK (ftkToSTK y)) of
        Just Refl -> second tscast $ evalFwdSame params s d
        _ -> (s, tdefTarget $ adFTK $ ftkDelta d0)
  DeltaSum0S (DeltaZero (FTKS _ x)) -> (s, tdefTarget (FTKS ZSS x))
  DeltaSum0S d -> case ftkDelta d of
    FTKS sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS sh $
      second tssum0 $ evalFwdSame params s d
  DeltaDot0S _ DeltaZero{} -> (s, tsconcrete $ Nested.sscalar 0)
  DeltaDot0S v d -> case ftkDelta d of
    FTKS sh FTKScalar ->
      withKnownShS sh $
      second (tsdot0 v) $ evalFwdSame params s d
  DeltaIndexS shn d ix -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS shn $
      withKnownShS (ixsToShS ix) $
      second (`tsindex` ix) $ evalFwdSame params s d
  DeltaScatterS @shm @shn shm shn shp d f -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS shm $
      withKnownShS shn $
      withKnownShS shp $
      let (s2, t) = evalFwdSame params s d
      in (s2, tsscatter @_ @shm @shn t f)
  DeltaGatherS @shm @shn shm shn shp d f -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShS shm $
      withKnownShS shn $
      withKnownShS shp $
      let (s2, t) = evalFwdSame params s d
      in (s2, tsgather @_ @shm @shn t f)
  DeltaAppendS d e -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      let (s2, t) = evalFwdSame params s d
          (s3, u) = evalFwdSame params s2 e
      in (s3, tsappend t u)
  DeltaSliceS i n k d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      second (tsslice i n k) $ evalFwdSame params s d
  DeltaReverseS d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      second tsreverse $ evalFwdSame params s d
  DeltaTransposeS perm d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      second (tstranspose perm) $ evalFwdSame params s d
  DeltaReshapeS sh2 d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (ftkToSTK x) $
      second (tsreshape sh2) $ evalFwdSame params s d
  DeltaZipS d -> case ftkDelta d of
    FTKProduct (FTKS _ y) (FTKS _ z) ->
      withKnownSTK (ftkToSTK y) $
      withKnownSTK (ftkToSTK z) $
      second szip $ evalFwdSame params s d
  DeltaUnzipS d -> second sunzip $ evalFwdSame params s d

  d0@(DeltaCastX d) -> case ftkDelta d of
    y ->
      case sameSTK (ftkToSTK y) (adSTK (ftkToSTK y)) of
        Just Refl -> second txcast $ evalFwdSame params s d
        _ -> (s, tdefTarget $ adFTK $ ftkDelta d0)
  DeltaSum0X (DeltaZero (FTKX _ x)) -> (s, tdefTarget (FTKX ZSX x))
  DeltaSum0X d -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX (ssxFromShX sh) $
      second txsum0 $ evalFwdSame params s d
  DeltaDot0X _ DeltaZero{} -> (s, txconcrete $ Nested.mscalar 0)
  DeltaDot0X v d -> case ftkDelta d of
    FTKX sh FTKScalar ->
      withKnownShX (ssxFromShX sh) $
      second (txdot0 v) $ evalFwdSame params s d
  DeltaIndexX @shm @shn shn d ix -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX shn $
-- TODO      withKnownShX (ixxToSSX ix) $
      withKnownShX (ssxTakeIx @shm @shn (ssxFromShX sh) ix) $
      second (`txindex` ix) $ evalFwdSame params s d
  DeltaScatterX @shm @shn shm shn shp sh d f -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX shm $
      withKnownShX shn $
      withKnownShX shp $
      let (s2, t) = evalFwdSame params s d
      in (s2, txscatter @_ @shm @shn sh t f)
  DeltaGatherX @shm @shn shm shn shp sh d f -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX shm $
      withKnownShX shn $
      withKnownShX shp $
      let (s2, t) = evalFwdSame params s d
      in (s2, txgather @_ @shm @shn sh t f)
  DeltaAppendX d e -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      let (s2, t) = evalFwdSame params s d
          (s3, u) = evalFwdSame params s2 e
      in (s3, txappend t u)
  DeltaSliceX i n k d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      second (txslice i n k) $ evalFwdSame params s d
  DeltaReverseX d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      second txreverse $ evalFwdSame params s d
  DeltaTransposeX perm d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      second (txtranspose perm) $ evalFwdSame params s d
  DeltaReshapeX sh2 d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (ftkToSTK x) $
      second (txreshape sh2) $ evalFwdSame params s d
  DeltaZipX d -> case ftkDelta d of
    FTKProduct (FTKX _ y) (FTKX _ z) ->
      withKnownSTK (ftkToSTK y) $
      withKnownSTK (ftkToSTK z) $
      second xzip $ evalFwdSame params s d
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
  DeltaCastCastable @a c1 astk bftk d ->
    -- This is implied by the form of c1.
    gcastWith (unsafeCoerceRefl :: ADTensorKind a :~: a) $
    second (tcastCastable c1 astk bftk) $ evalFwdSame params s d

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
      withKnownShX (ssxFromShX sh1) $
      second xunNestR $ evalFwdSame params s d
  DeltaXUnNestS d -> case ftkDelta d of
    FTKX sh1 (FTKS sh2 x) ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX (ssxFromShX sh1) $
      withKnownShS sh2 $
      second xunNestS $ evalFwdSame params s d
  DeltaXUnNest d -> case ftkDelta d of
    FTKX sh1 (FTKX sh2 x) ->
      withKnownSTK (ftkToSTK x) $
      withKnownShX (ssxFromShX sh1) $
      withKnownShX (ssxFromShX sh2) $
      second xunNest $ evalFwdSame params s d

  d -> evalFwd params s d
