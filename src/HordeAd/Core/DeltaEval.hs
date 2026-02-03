{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Evaluation of delta expressions, that is, transpose of the linear
-- maps of which the delta expressions are sparse representations.
-- See comments in "HordeAd.Core.Delta".
module HordeAd.Core.DeltaEval
  ( -- * Delta expression evaluation
    gradientFromDelta, derivativeFromDelta
  ) where

import Prelude

import Control.Arrow (second)
import Control.Exception.Assert.Sugar
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Text.Show (showListWith)
import Text.Show.Functions ()
import Type.Reflection (typeRep)

import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation (permInverse)
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped qualified as Shaped
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd.Core.Conversion
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
  -> target (ADTensorKind z)
  -> Delta target z
  -> target (ADTensorKind x)
gradientFromDelta !xftk !dt deltaTopLevel =
  let s0 = initEvalState xftk
      s1 = evalRev s0 dt deltaTopLevel
      s2 = evalRevFromnMap s1
      (res, remainder) =
        rebuildInputs @(ADTensorKind x) (DMap.toAscList $ iMap s2) s2
        $ adFTK xftk
  in assert (null remainder) res

-- | The top-level function for computing a (forward) derivative
-- of an objective function.
derivativeFromDelta
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => Proxy x -> Delta target z -> FullShapeTK (ADTensorKind x)
  -> target (ADTensorKind x)
  -> target (ADTensorKind z)
derivativeFromDelta _ deltaTopLevel ftk ds =
    let iMap = DMap.fromDistinctAscList $ fst $ generateDSums 0 ftk ds
        s0 = DMap.empty
        !(!_s2, !c) = evalFwd iMap s0 deltaTopLevel
    in c


-- * Auxiliary datatypes for Delta evaluation

type ADMap target = DEnumMap (NodeId target) (Cotangent target)

type IMap target = DEnumMap (InputId target) (TensorOrZero target)

showsPrec_IMap
  :: AllTargetShow target
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
  :: AllTargetShow target
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
addTensorOrZero
  :: forall target y. (TKAllNum y, ADReadyNoLet target, ShareTensor target)
  => SingletonTK y -> TensorOrZero target y -> TensorOrZero target y
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
  :: forall y target. (ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalRev !s !c d0 = case d0 of
  DeltaShare n d | Dict0 <- lemTKAllNumAD (ftkToSTK $ nodeIdToFTK n) ->
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
  DeltaInput i | Dict0 <- lemTKAllNumAD (ftkToSTK $ inputIdToFTK i) ->
    -- This is true for DeltaInput by construction:
    gcastWith (unsafeCoerceRefl :: ADTensorKind y :~: y) $
    let cs = TOTensor c
    in s {iMap = DMap.adjust (addTensorOrZero (ftkToSTK $ inputIdToFTK i) cs) i
                 $ iMap s}
    -- Note that we can't express sharing by inserting DeltaShare constructors
    -- into iMap, because often sharing needs to work across many
    -- iMap keys. That's why global sharing is used.

  DeltaPair d1 d2 ->
    let (c1, c2) = tunpair c
    in evalRev (evalRev s c1 d1) c2 d2
  DeltaProject1 d -> case ftkDelta d of
    FTKProduct _ ftk2 ->
      let zero = tdefTarget $ adFTK ftk2
      in evalRev s (tpair c zero) d
    -- if y is, e.g., TKR 0 Int, we eval this delta anyway, even though
    -- we could ignore it at the price of complicating or duplicating
    -- the code slightly more
  DeltaProject2 d -> case ftkDelta d of
    FTKProduct ftk1 _ ->
      let zero = tdefTarget $ adFTK ftk1
      in evalRev s (tpair zero c) d
  DeltaFromVector snat stk ld | Refl <- lemBuildOfAD snat stk ->
    let cxs = tunravelToListShare snat (adSTK stk) c
    in foldl' (\ !s2 (cx, d2) -> evalRev s2 cx d2) s
       $ zip cxs (V.toList ld)
  DeltaSum snat stk d | Refl <- lemBuildOfAD snat stk ->
    evalRev s (treplicate snat (adSTK stk) c) d
  DeltaReplicate snat stk d | Refl <- lemBuildOfAD snat stk
                            , Dict0 <- lemTKAllNumAD stk ->
    evalRev s (tsum snat (adSTK stk) c) d
  DeltaMapAccumL k (FTKScalar @z1) eftk
                 as es _df rf acc0' es' -- special case to speed up folds
   | Just Refl <- testEquality (typeRep @z1) (typeRep @Z1)
   , Refl <- lemBuildOfAD k (ftkToSTK eftk) ->
    let accftk = ftkDelta acc0'
        accftkAD = adFTK accftk
        eftkAD = adFTK eftk
        (c0, _crest) = tunpair c
        dacc_des =
          tmapAccumR (Proxy @target)
                     k accftkAD eftkAD (FTKProduct accftk eftk)
                     (\dx acc_e ->
                        unHFun rf (tpair (tpair dx (tkconcrete Z1)) acc_e))
                     c0
                     (tpair as es)
        (dacc, des) = tunpair dacc_des
        s2 = evalRev s dacc acc0'
    in evalRev s2 des es'
  DeltaMapAccumL k bftk eftk as es _df rf acc0' es'
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
                     (tpair crest (tpair as es))
        (dacc, des) = tunpair dacc_des
        s2 = evalRev s dacc acc0'
    in evalRev s2 des es'

  DeltaZero{} -> s
  DeltaScale (NestedTarget k) d ->
    let z = ftkDelta d
    in case matchingFTK z (adFTK z) of
         Just Refl -> evalRev s (k * c) d
         _ -> s
  DeltaAdd d e ->
    let cShared = tshare c
    in evalRev (evalRev s cShared d) cShared e

  DeltaCastK d -> evalRev s (tkcast c) d

  DeltaCastR d -> evalRev s (trcast c) d
  DeltaSum0R d -> case adFTK $ ftkDelta d of
    FTKR sh FTKScalar | SNat <- shrRank sh ->
      evalRev s (trreplicate0N sh c) d
  DeltaDot0R @r v d ->
    ifDifferentiable @r
      (case ftkDelta d of
         FTKR sh FTKScalar | SNat <- shrRank sh ->
           evalRev s (v * trreplicate0N sh c) d)
      s
  DeltaIndexR SNat d ix -> case ftkDelta d of
    FTKR sh x | SNat <- ixrRank ix
              , Dict0 <- lemTKAllNumAD (ftkToSTK x) ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      evalRev s (troneHot (shrTake sh) c ix) d
  DeltaScatterR SNat SNat SNat _sh d f -> case ftkDelta d of
    FTKR sh x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      evalRev s (trgather sh c f) d
  DeltaGatherR SNat SNat SNat _sh d f -> case ftkDelta d of
    FTKR sh x | Dict0 <- lemTKAllNumAD (ftkToSTK x) ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      evalRev s (trscatter sh c f) d
  DeltaAppendR d e -> case (ftkDelta d, ftkDelta e) of
    (FTKR (m :$: _) x, FTKR (n :$: _) _) ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      let cShared = tshare c
          s2 = evalRev s (trslice 0 m cShared) d
      in evalRev s2 (trslice m n cShared) e
    _ -> error "evalRev: impossible pattern needlessly required"
  -- Depite the warning, the pattern match is exhaustive and if a dummy
  -- pattern is added, GHC 9.14.1 complains about that, in turn.
  DeltaSliceR i n d -> case ftkDelta d of
    FTKR (l :$: rest) x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      evalRev s (trappend
                   (tdefTarget (FTKR (i :$: rest) (adFTK x)))
                   (trappend c
                      (tdefTarget (FTKR (l - i - n :$: rest) (adFTK x))))) d
  DeltaReverseR d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      evalRev s (trreverse c) d
  DeltaTransposeR perm d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      let permR = permRInverse perm
      in evalRev s (trtranspose permR c) d
  DeltaReshapeR _sh2 d -> case ftkDelta d of
    FTKR sh x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      evalRev s (trreshape sh c) d

  DeltaCastS d -> evalRev s (tscast c) d
  DeltaSum0S d -> case adFTK $ ftkDelta d of
    FTKS sh FTKScalar ->
      evalRev s (tsreplicate0N sh c) d
  DeltaDot0S @r v d ->
    ifDifferentiable @r
      (case ftkDelta d of
         FTKS sh FTKScalar->
           evalRev s (v * tsreplicate0N sh c) d)
      s
  DeltaIndexS @shm @shn shn d ix -> case ftkDelta d of
    FTKS sh x | Dict0 <- lemTKAllNumAD (ftkToSTK x) ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      withKnownShS shn $
      withKnownShS (Shaped.shsTakeIx @shn @shm Proxy sh ix) $
      evalRev s (tsoneHot c ix) d
  DeltaScatterS @shm @shn shm shn shp d f -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      withKnownShS shm $
      withKnownShS shn $
      withKnownShS shp $
      evalRev s (tsgather @_ @shm @shn c f) d
  DeltaGatherS @shm @shn shm shn shp d f -> case ftkDelta d of
    FTKS _ x | Dict0 <- lemTKAllNumAD (ftkToSTK x) ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      withKnownShS shm $
      withKnownShS shn $
      withKnownShS shp $
      evalRev s (tsscatter @_ @shm @shn c f) d
  DeltaAppendS d e -> case (ftkDelta d, ftkDelta e) of
    (FTKS (msnat :$$ _) x, FTKS (nsnat :$$ _) _) ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      let cShared = tshare c
          s2 = evalRev s (tsslice (SNat @0) msnat nsnat cShared) d
      in evalRev s2 (tsslice msnat nsnat SNat cShared) e
  DeltaSliceS i@SNat _ k@SNat d -> case ftkDelta d of
    FTKS (_ :$$ sh) x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      evalRev s (tsappend
                       (tdefTarget (FTKS (i :$$ sh) (adFTK x)))
                          (tsappend
                             c (tdefTarget (FTKS (k :$$ sh) (adFTK x))))) d
  DeltaReverseS d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      evalRev s (tsreverse c) d
  DeltaTransposeS @perm @sh2 perm d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      permInverse perm $ \(permRev :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix
                        permR (Permutation.PermutePrefix perm sh2) :~: sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank (Permutation.PermutePrefix perm sh2) :~: Rank sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank permR :~: Rank perm)
        $ evalRev s (tstranspose permRev c) d
  DeltaReshapeS _sh2 d -> case ftkDelta d of
    FTKS sh x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      evalRev s (tsreshape sh c) d

  DeltaCastX d -> evalRev s (txcast c) d
  DeltaSum0X d -> case adFTK $ ftkDelta d of
    FTKX sh FTKScalar ->
      withKnownShX (ssxFromShX sh) $
      evalRev s (txreplicate0N sh c) d
  DeltaDot0X @r v d ->
    ifDifferentiable @r
      (case ftkDelta d of
         FTKX sh FTKScalar ->
           withKnownShX (ssxFromShX sh) $
           evalRev s (v * txreplicate0N sh c) d)
      s
  DeltaIndexX @shm @shn shn d ix -> case ftkDelta d of
    FTKX sh x | SNat @len <- ixxRank ix
              , Dict0 <- lemTKAllNumAD (ftkToSTK x) ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      withKnownShX shn $
      withKnownShX (ssxTakeIx @shm @shn Proxy ix (ssxFromShX sh)) $
      gcastWith (unsafeCoerceRefl :: Take (Rank shm) (shm ++ shn) :~: shm) $
      evalRev s (txoneHot (shxTake @len sh) c ix) d
--TODO      evalRev s (xoneHot (shxTakeSSX (Proxy @shn) sh
--                                         (ssxFromIxX ix)) c ix) d
  DeltaScatterX @shm @shn shm shn shp _sh d f -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      withKnownShX shm $
      withKnownShX shn $
      withKnownShX shp $
      evalRev s (txgather @_ @shm @shn sh c f) d
  DeltaGatherX @shm @shn shm shn shp _sh d f -> case ftkDelta d of
    FTKX sh x | Dict0 <- lemTKAllNumAD (ftkToSTK x) ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      withKnownShX shm $
      withKnownShX shn $
      withKnownShX shp $
      evalRev s (txscatter @_ @shm @shn sh c f) d
  DeltaAppendX d e -> case (ftkDelta d, ftkDelta e) of
    (FTKX (Nested.SKnown m@SNat :$% _) x, FTKX (Nested.SKnown SNat :$% _) _) ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      let cShared = tshare c
          s2 = evalRev s (txslice (SNat @0) SNat SNat cShared) d
      in evalRev s2 (txslice m SNat SNat cShared) e
  DeltaSliceX i@SNat _ k@SNat d -> case ftkDelta d of
    FTKX (_ :$% sh) x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      evalRev s (txappend
                   (tdefTarget (FTKX (Nested.SKnown i :$% sh) (adFTK x)))
                      (txappend
                         c (tdefTarget
                              (FTKX (Nested.SKnown k :$% sh) (adFTK x))))) d
  DeltaReverseX d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      evalRev s (txreverse c) d
  DeltaTransposeX @perm @sh2 perm d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      permInverse perm $ \(permR :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix
                        permR (Permutation.PermutePrefix perm sh2) :~: sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Rank (Permutation.PermutePrefix perm sh2) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Rank permR :~: Rank perm) $
        evalRev s (txtranspose permR c) d
  DeltaReshapeX _sh2 d -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      evalRev s (txreshape sh c) d

  DeltaConvert c1 d ->
    let z = ftkDelta d
    in case matchingFTK z (adFTK z) of
         Just Refl ->
           -- This follows from the property of conversions reflecting
           -- the underlying scalar types unchanged.
           gcastWith (unsafeCoerceRefl :: ADTensorKind y :~: y) $
           evalRev s (tconvert (transposeTKConversion (ftkDelta d) c1)
                   (convertSTK c1 $ ftkToSTK $ ftkDelta d) c) d
         _ -> s

evalRevFromnMap :: forall target. (ADReadyNoLet target, ShareTensor target)
                => EvalState target -> EvalState target
evalRevFromnMap s@EvalState{nMap, dMap} =
  case DMap.maxViewWithKey nMap of
    Just (n :=> d, nMap2) ->
      let s2 = s {nMap = nMap2}
          s3 = case DMap.lookup n dMap of
            Just (Cotangent c) -> evalRev s2 c d
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
evalFwd params !s d0 = case d0 of
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
    let (s2, l) = mapAccumL' (evalFwd params) s $ V.toList lsd
    in (s2, tfromVector snat (adSTK stk) $ V.fromListN (V.length lsd) l)
  DeltaSum snat stk d | Refl <- lemBuildOfAD snat stk
                      , Dict0 <- lemTKAllNumAD stk ->
    let (s2, t) = evalFwd params s d
    in (s2, tsum snat (adSTK stk) t)
  DeltaReplicate snat stk d | Refl <- lemBuildOfAD snat stk ->
    let (s2, t) = evalFwd params s d
    in (s2, treplicate snat (adSTK stk) t)
  -- No special case to speed up folds, because the concrete tmapAccumLDer
  -- does the very Z1 optimization that could be performed here.
  DeltaMapAccumL k bftk eftk as es df _rf acc0' es'
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
                       (tpair ces (tpair as es)))

  DeltaZero ftk -> (s, tdefTarget $ adFTK ftk)
  DeltaScale (NestedTarget k) d ->
    let z = ftkDelta d
    in case matchingFTK z (adFTK z) of
         Just Refl -> second (* k) $ evalFwd params s d
         _ -> (s, tdefTarget $ adFTK z)
  DeltaAdd d e ->
    let y = ftkDelta d0  -- either d or e may be DeltaShare
    in case matchingFTK y (adFTK y) of
         Just Refl ->
           let (s2, t) = evalFwd params s d
               (s3, u) = evalFwd params s2 e
           in (s3, t + u)
         _ -> (s, tdefTarget $ adFTK y)

  DeltaCastK d -> second tkcast $ evalFwd params s d

  DeltaCastR d -> second trcast $ evalFwd params s d
  DeltaSum0R @r DeltaZero{} -> (s, toADTensorKindShared (FTKScalar @r) 0)
  DeltaSum0R @r d ->
    ifDifferentiable @r
      (case ftkDelta d of
         FTKR sh FTKScalar | SNat <- shrRank sh ->
           second trsum0 $ evalFwd params s d)
      (s, toADTensorKindShared (FTKScalar @r) 0)
  DeltaDot0R @r _ DeltaZero{} -> (s, toADTensorKindShared (FTKScalar @r) 0)
  DeltaDot0R @r v d ->
    ifDifferentiable @r
      (case ftkDelta d of
         FTKR sh FTKScalar | SNat <- shrRank sh ->
           second (trdot0 v) $ evalFwd params s d)
      (s, toADTensorKindShared (FTKScalar @r) 0)
  DeltaIndexR SNat d ix -> case ftkDelta d of
    FTKR _ x | SNat <- ixrRank ix ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second (`trindex` ix) $ evalFwd params s d
  DeltaScatterR SNat SNat SNat sh d f -> case ftkDelta d of
    FTKR _ x | Dict0 <- lemTKAllNumAD (ftkToSTK x) ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      let (s2, t) = evalFwd params s d
      in (s2, trscatter sh t f)
  DeltaGatherR SNat SNat SNat sh d f -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      let (s2, t) = evalFwd params s d
      in (s2, trgather sh t f)
  DeltaAppendR d e -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      let (s2, t) = evalFwd params s d
          (s3, u) = evalFwd params s2 e
      in (s3, trappend t u)
  DeltaSliceR i n d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second (trslice i n) $ evalFwd params s d
  DeltaReverseR d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second trreverse $ evalFwd params s d
  DeltaTransposeR perm d -> case ftkDelta d of
    FTKR _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second (trtranspose perm) $ evalFwd params s d
  DeltaReshapeR sh2 d -> case ftkDelta d of
    FTKR _sh x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second (trreshape sh2) $ evalFwd params s d

  DeltaCastS d -> second tscast $ evalFwd params s d
  DeltaSum0S @r DeltaZero{} -> (s, toADTensorKindShared (FTKScalar @r) 0)
  DeltaSum0S @r d ->
    ifDifferentiable @r
      (case ftkDelta d of
         FTKS sh FTKScalar ->
           withKnownShS sh $
           second tssum0 $ evalFwd params s d)
      (s, toADTensorKindShared (FTKScalar @r) 0)
  DeltaDot0S @r _ DeltaZero{} -> (s, toADTensorKindShared (FTKScalar @r) 0)
  DeltaDot0S @r v d ->
    ifDifferentiable @r
      (case ftkDelta d of
         FTKS sh FTKScalar ->
           withKnownShS sh $
           second (tsdot0 v) $ evalFwd params s d)
      (s, toADTensorKindShared (FTKScalar @r) 0)
  DeltaIndexS shn d ix -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      withKnownShS shn $
      second (`tsindex` ix) $ evalFwd params s d
  DeltaScatterS @shm @shn shm shn shp d f -> case ftkDelta d of
    FTKS _ x | Dict0 <- lemTKAllNumAD (ftkToSTK x) ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      withKnownShS shm $
      withKnownShS shn $
      withKnownShS shp $
      let (s2, t) = evalFwd params s d
      in (s2, tsscatter @_ @shm @shn t f)
  DeltaGatherS @shm @shn shm shn shp d f -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      withKnownShS shm $
      withKnownShS shn $
      withKnownShS shp $
      let (s2, t) = evalFwd params s d
      in (s2, tsgather @_ @shm @shn t f)
  DeltaAppendS d e -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      let (s2, t) = evalFwd params s d
          (s3, u) = evalFwd params s2 e
      in (s3, tsappend t u)
  DeltaSliceS i n k d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second (tsslice i n k) $ evalFwd params s d
  DeltaReverseS d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second tsreverse $ evalFwd params s d
  DeltaTransposeS perm d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second (tstranspose perm) $ evalFwd params s d
  DeltaReshapeS sh2 d -> case ftkDelta d of
    FTKS _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second (tsreshape sh2) $ evalFwd params s d

  DeltaCastX d -> second txcast $ evalFwd params s d
  DeltaSum0X @r DeltaZero{} -> (s, toADTensorKindShared (FTKScalar @r) 0)
  DeltaSum0X @r d ->
    ifDifferentiable @r
      (case ftkDelta d of
         FTKX sh FTKScalar ->
           withKnownShX (ssxFromShX sh) $
           second txsum0 $ evalFwd params s d)
      (s, toADTensorKindShared (FTKScalar @r) 0)
  DeltaDot0X @r _ DeltaZero{} -> (s, toADTensorKindShared (FTKScalar @r) 0)
  DeltaDot0X @r v d ->
    ifDifferentiable @r
      (case ftkDelta d of
         FTKX sh FTKScalar ->
           withKnownShX (ssxFromShX sh) $
           second (txdot0 v) $ evalFwd params s d)
      (s, toADTensorKindShared (FTKScalar @r) 0)
  DeltaIndexX @shm @shn shn d ix -> case ftkDelta d of
    FTKX sh x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      withKnownShX shn $
      withKnownShX (ssxTakeIx @shm @shn Proxy ix (ssxFromShX sh)) $
      second (`txindex` ix) $ evalFwd params s d
  DeltaScatterX @shm @shn shm shn shp sh d f -> case ftkDelta d of
    FTKX _ x | Dict0 <- lemTKAllNumAD (ftkToSTK x) ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      withKnownShX shm $
      withKnownShX shn $
      withKnownShX shp $
      let (s2, t) = evalFwd params s d
      in (s2, txscatter @_ @shm @shn sh t f)
  DeltaGatherX @shm @shn shm shn shp sh d f -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      withKnownShX shm $
      withKnownShX shn $
      withKnownShX shp $
      let (s2, t) = evalFwd params s d
      in (s2, txgather @_ @shm @shn sh t f)
  DeltaAppendX d e -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      let (s2, t) = evalFwd params s d
          (s3, u) = evalFwd params s2 e
      in (s3, txappend t u)
  DeltaSliceX i n k d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second (txslice i n k) $ evalFwd params s d
  DeltaReverseX d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second txreverse $ evalFwd params s d
  DeltaTransposeX perm d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second (txtranspose perm) $ evalFwd params s d
  DeltaReshapeX sh2 d -> case ftkDelta d of
    FTKX _ x ->
      withKnownSTK (adSTK $ ftkToSTK x) $
      second (txreshape sh2) $ evalFwd params s d

  DeltaConvert c1 d ->
    let z = ftkDelta d
    in case matchingFTK z (adFTK z) of
         Just Refl ->
           -- This follows from the property of conversions reflecting
           -- the underlying scalar types unchanged.
           gcastWith (unsafeCoerceRefl :: ADTensorKind y :~: y) $
           second (tconvert c1 (ftkToSTK (ftkDelta d)))
                  (evalFwd params s d)
         _ -> (s, tdefTarget $ adFTK $ ftkDelta d0)
