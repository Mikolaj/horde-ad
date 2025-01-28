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
import GHC.TypeLits (KnownNat, sameNat, type (+))
import Text.Show (showListWith)
import Text.Show.Functions ()
import Type.Reflection (typeRep)

import Data.Array.Mixed.Permutation (permInverse)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (shxTakeSSX, ssxFromShape, withKnownShX)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested
  (IShR, KnownShS (..), KnownShX (..), Rank, ShR (..), ShS (..), ShX (..))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape
  (shrRank, shsPermutePrefix, shsProduct, shsRank, withKnownShS)

import HordeAd.Core.Delta
import HordeAd.Core.HVectorOps
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Computing derivatives from delta expressions

type IMap target = DEnumMap (InputId target) (RepM target)

type ADMap target = DEnumMap (NodeId target) (RepAD target)

gradientFromDelta
  :: forall x z target.
     (ADReadyNoLet target, ShareTensor target, TensorKind z)
  => FullTensorKind x
  -> target z
  -> Maybe (target (ADTensorKind z))
  -> Delta target z
  -> target (ADTensorKind x)
gradientFromDelta !parameters0 value !mdt deltaTopLevel =
  let oneAtF = constantTarget 1 $ aDFTK $ tftk (stensorKind @z) value
      dt = fromMaybe oneAtF mdt
      s0 = initEvalState parameters0
      s1 = evalRev s0 dt deltaTopLevel
      s2 = evalRevFromnMap s1
      rebuildInputs :: forall ady.  -- ady ~ ADTensorKind y
                       [Some (RepM target)] -> FullTensorKind ady
                    -> (target ady, [Some (RepM target)])
      rebuildInputs els = \case
        FTKScalar @r -> case els of
          Some mt@(MTKScalar @r2 t) : rest ->
            case testEquality (typeRep @r) (typeRep @r2) of
              Just Refl -> (t, rest)
              _ -> error $ "gradientFromDelta: wrong type: " ++ show mt
          Some mt@(MTKScalarDummy @r2) : rest
            | Just Refl <- testEquality (typeRep @r) (typeRep @r2) ->
              (evalRepM mt, rest)
          _ -> error $ "gradientFromDelta: illegal RepM: "
                       ++ show_iMap (iMap s2)
        FTKR @n sh x | SNat <- shrRank sh
                     , Dict <- lemTensorKindOfSTK (ftkToStk x) -> case els of
          Some mt@(MTKR @r2 @n2 t) : rest ->
            case ( sameNat (Proxy @n) (Proxy @n2)
                 , sameSTK (ftkToStk x) (stensorKind @r2) ) of
              (Just Refl, Just Refl) -> (t, rest)
              _ -> error $ "gradientFromDelta: wrong type: " ++ show mt
                           ++ " instead of "
                           ++ "FTKR @" ++ show (valueOf @n :: Int)
                           ++ " within " ++ show_iMap (iMap s2)
          Some mt@(MTKRDummy @_ @n2 sh2 x2) : rest
            | SNat <- shrRank sh2
            , Just Refl <- sameNat (Proxy @n) (Proxy @n2)  -- TODO: compare sh
            , Just Refl <- sameSTK (ftkToStk x) (ftkToStk x2) ->  -- TODO: compare ftk
              (evalRepM mt, rest)
          _ -> error $ "gradientFromDelta: illegal RepM: "
                       ++ show_iMap (iMap s2)
        FTKS @sh sh x | Dict <- lemTensorKindOfSTK (ftkToStk x) ->
          withKnownShS sh $ case els of
            Some mt@(MTKS @r2 @sh2 t) : rest ->
              case ( sameShape @sh @sh2
                   , sameSTK (ftkToStk x) (stensorKind @r2) ) of
                (Just Refl, Just Refl) -> (t, rest)
                _ -> error $ "gradientFromDelta: wrong type: " ++ show mt
                             ++ " instead of "
                             ++ "FTKS @" ++ show (knownShS @sh)
                             ++ " within " ++ show_iMap (iMap s2)
            Some mt@(MTKSDummy sh2 x2) : rest
              | Just Refl <- testEquality sh sh2
              , Just Refl <- sameSTK (ftkToStk x) (ftkToStk x2) ->
                (evalRepM mt, rest)
            _ -> error $ "gradientFromDelta: illegal RepM: "
                         ++ show_iMap (iMap s2)
        FTKX{} -> error "TODO"
        FTKProduct @y1 @y2 ftk1 ftk2
         | Dict <- lemTensorKindOfSTK (ftkToStk ftk1)
         , Dict <- lemTensorKindOfSTK (ftkToStk ftk2) ->
            let (t1, rest1) = rebuildInputs @y1 els ftk1
                (t2, rest2) = rebuildInputs @y2 rest1 ftk2
            in (tpair t1 t2, rest2)
      (res, remainder) = rebuildInputs @(ADTensorKind x) (DMap.elems $ iMap s2)
                         $ aDFTK parameters0
  in assert (null remainder) res

showsPrec_iMap
  :: (forall y. TensorKind y => Show (RepM target y))
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
  :: (forall y. TensorKind y => Show (RepM target y))
  => IMap target -> String
show_iMap iMap = showsPrec_iMap 0 iMap ""

derivativeFromDelta
  :: forall x z target.
     ( ADReadyNoLet target, ShareTensor target, TensorKind x, TensorKind z )
  => Delta target z -> target (ADTensorKind x)
  -> target (ADTensorKind z)
derivativeFromDelta deltaTopLevel ds | Dict <- lemTensorKindOfAD (stensorKind @x) =
  let -- Matches generateDeltaInputs.
      generateDSums :: Int -> FullTensorKind y -> target y
                    -> ( [DSum (InputId target) (RepM target)]
                       , Int )
      generateDSums j ftk t = case ftk of
        FTKScalar @r -> ([InputId j :=> MTKScalar @r t], j + 1)
        FTKR sh x | SNat <- shrRank sh
                  , Dict <- lemTensorKindOfSTK (ftkToStk x) ->
          ([InputId j :=> MTKR t], j + 1)
        FTKS sh x | Dict <- lemTensorKindOfSTK (ftkToStk x) ->
          withKnownShS sh $
          ([InputId j :=> MTKS t], j + 1)
        FTKX{} -> error "TODO"
        FTKProduct ftk1 ftk2 | Dict <- lemTensorKindOfSTK (ftkToStk ftk1)
                             , Dict <- lemTensorKindOfSTK (ftkToStk ftk2) ->
          let (t1, t2) = tunpair t
              (ds1, j1) = generateDSums j ftk1 t1
              (ds2, j2) = generateDSums j1 ftk2 t2
          in (ds1 ++ ds2, j2)
      iMap = DMap.fromDistinctAscList $ fst
             $ generateDSums 0 (tftk stensorKind ds) ds
      s0 = DMap.empty
      !(!_s2, !c) = evalFwd iMap s0 deltaTopLevel
  in c


-- * Auxiliary datatypes for Delta evaluation

evalRepM :: forall target x. ADReadyNoLet target
         => RepM target x -> target x
evalRepM = \case
  MTKScalar t -> t
  MTKR t -> t
  MTKS t -> t
  MTKScalarDummy -> kconcrete 0
  MTKRDummy shr ftk -> constantTarget 0 (FTKR shr ftk)
  MTKSDummy sh ftk -> constantTarget 0 (FTKS sh ftk)

repToM
  :: STensorKindType x -> target x
  -> RepM target x
repToM stk t = case stk of
  STKScalar{} -> MTKScalar t
  STKR SNat x | Dict <- lemTensorKindOfSTK x -> MTKR t
  STKS sh x | Dict <- lemTensorKindOfSTK x -> withKnownShS sh $ MTKS t
  STKX sh x | Dict <- lemTensorKindOfSTK x -> withKnownShX sh $ error "TODO"
  STKProduct{} -> error "repToM: unexpected type"

addRepM :: forall target y. ADReadyNoLet target
        => RepM target y -> RepM target y -> RepM target y
addRepM a b = case (a, b) of
  (MTKScalar ta, MTKScalar tb) -> MTKScalar $ ta + tb
  (MTKR ta, MTKR tb) | STKR _ STKScalar{} <- stensorKind @y -> MTKR $ ta + tb
  (MTKR ta, MTKR tb) -> MTKR $ addTarget stensorKind ta tb
    -- target has a ShareTensor instance, so ta and tb don't need
    -- to be duplicable
  (MTKScalarDummy, _) -> b
  (_, MTKScalarDummy) -> a
  (MTKRDummy{}, _) -> b
  (_, MTKRDummy{}) -> a
  (MTKS ta, MTKS tb) | STKS _ STKScalar{} <- stensorKind @y -> MTKS $ ta + tb
  (MTKS ta, MTKS tb) -> MTKS $ addTarget stensorKind ta tb
  (MTKSDummy{}, _) -> b
  (_, MTKSDummy{}) -> a

type role RepM nominal nominal
data RepM target y where
  MTKScalar :: GoodScalar r
            => target (TKScalar r)
            -> RepM target (TKScalar r)
  MTKR :: (TensorKind r, KnownNat n)
       => target (TKR2 n r)
       -> RepM target (TKR2 n r)
  MTKS :: (TensorKind r, KnownShS sh)
       => target (TKS2 sh r)
       -> RepM target (TKS2 sh r)
  MTKScalarDummy :: GoodScalar r
                 => RepM target (TKScalar r)
  MTKRDummy :: forall x n target.
               IShR n -> FullTensorKind x
            -> RepM target (TKR2 n x)
  MTKSDummy  :: forall x sh target.
                ShS sh -> FullTensorKind x
             -> RepM target (TKS2 sh x)

deriving instance ( (forall y7. TensorKind y7 => Show (target y7))
                  , TensorKind y )
                  => Show (RepM target y)

type role RepAD nominal nominal
newtype RepAD target y =
  RepAD {unRepAD :: target (ADTensorKind y)}


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
  let -- Matches generateDeltaInputs.
      generateDSums :: Int -> FullTensorKind y
                    -> ([DSum (InputId target) (RepM target)], Int)
      generateDSums j ftk  = case ftk of
        FTKScalar @r -> ([InputId j :=> MTKScalarDummy @r], j + 1)
        FTKR shr x | SNat <- shrRank shr
                   , Dict <- lemTensorKindOfSTK (ftkToStk x) ->
          ([InputId j :=> MTKRDummy shr x], j + 1)
        FTKS sh x | Dict <- lemTensorKindOfSTK (ftkToStk x) ->
          withKnownShS sh $
          ([InputId j :=> MTKSDummy sh x], j + 1)
        FTKX{} -> error "TODO"
        FTKProduct ftk1 ftk2 ->
          let (ds1, j1) = generateDSums j ftk1
              (ds2, j2) = generateDSums j1 ftk2
          in (ds1 ++ ds2, j2)
      -- Create finite maps that hold values associated with inputs
      -- and with (possibly shared) term tree nodes.
      -- The former are usually initialized with dummy values so that it's cheap
      -- to check if any update has already been performed to a cell
      -- (allocating big vectors filled with zeros is too costly,
      -- especially if never used in an iteration, and adding to such vectors
      -- and especially using them as cotangent accumulators is wasteful.
      -- We take care to keep the scalar type of the dummy correct,
      -- but a shape is not preserved in a dummy, so it's not shape-correct.
      iMap = DMap.fromDistinctAscList $ fst $ generateDSums 0
             $ aDFTK ftk0
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
     (TensorKind y, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalRev !s !c d0 = case d0 of
  -- All constructors that admit a TKProduct kind need to be handled in evalRev
  -- except for DeltaInput that is always constructed only in basic kinds.
  DeltaPair @y1 @y2 d1 d2 | Dict <- lemTensorKindOfAD (stensorKind @y1)
                      , Dict <- lemTensorKindOfAD (stensorKind @y2) ->
    let (c1, c2) = tunpair c
    in evalRev (evalRev s c1 d1) c2 d2
  DeltaProject1 @_ @z d | Dict <- lemTensorKindOfAD (stensorKind @y)
                    , Dict <- lemTensorKindOfAD (stensorKind @z) ->
    case shapeDeltaFull d of
      FTKProduct _ ftk2 ->
        let zero = constantTarget 0 $ aDFTK ftk2
        in evalRev s (tpair c zero) d
    -- if y is, e.g., TKR Int 0, we eval this delta even though we could ignore it
    -- at the price of complicating or duplicating the code slightly more
  DeltaProject2 @x d | Dict <- lemTensorKindOfAD (stensorKind @y)
                 , Dict <- lemTensorKindOfAD (stensorKind @x) ->
    case shapeDeltaFull d of
      FTKProduct ftk1 _ ->
        let zero = constantTarget 0 $ aDFTK ftk1
        in evalRev s (tpair zero c) d
  DeltaFromVector snat stk ld | Refl <- lemBuildOfAD snat stk
                          , Dict <- lemTensorKindOfAD (stensorKind @y) ->
    let cShared = tshare c
        cxs = tunravelToListShare snat (aDSTK stk) cShared
    in foldl' (\ !s2 (cx, d2) -> evalRev s2 cx d2) s
       $ zip cxs (V.toList ld)
  DeltaSum snat stk d | Refl <- lemBuildOfAD snat stk ->
    evalRev s (treplicateShare snat (aDSTK stk) c) d
  DeltaReplicate snat stk d | Refl <- lemBuildOfAD snat stk ->
    evalRev s (tsumShare snat (aDSTK stk) c) d
  DeltaShare n d | Dict <- lemTensorKindOfAD (stensorKind @y) ->
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
          let addc x = RepAD $ addTarget stensorKind c (unRepAD x)
            -- target has a ShareTensor instance, so addTarget arguments
            -- don't need to be duplicable
          in s {dMap = DMap.adjust addc n $ dMap s}
        Nothing ->
          let cd = RepAD c
          in s { nMap = DMap.insert n d $ nMap s
               , dMap = DMap.insert n cd $ dMap s }
  DeltaMapAccumR @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            _df rf acc0' es'
   | Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind bShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDFTK accShs
        bShsAD = aDFTK bShs
        eShsAD = aDFTK eShs
        (c0, crest) = tunpair c
        dacc_des =
          dmapAccumL (Proxy @target)
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
   | Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind bShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDFTK accShs
        bShsAD = aDFTK bShs
        eShsAD = aDFTK eShs
        (c0, crest) = tunpair c
        dacc_des =
          dmapAccumR (Proxy @target)
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
  DeltaFromS @_ @z (DeltaSFromR @sh @x d)
    | Just Refl <- sameSTK (aDSTK (stensorKind @z))
                           (aDSTK (stensorKind @(TKR2 (Rank sh) x))) ->
      evalRev s c d
  DeltaFromS @_ @z (DeltaSFromX @_ @sh' @x d)
    | Just Refl <- sameSTK (aDSTK (stensorKind @z))
                           (aDSTK (stensorKind @(TKX2 sh' x))) ->
      evalRev s c d
  DeltaFromS @y7 @z d -> case (stensorKind @y7, stensorKind @z) of
    (stky, stkz) | Just Refl <- sameSTK stky stkz -> evalRev s c d
    (STKS ZSS yx@(STKScalar try), STKScalar trz) ->
      case testEquality try trz of
        Just Refl -> case sameSTK yx (aDSTK yx) of
          Just Refl -> evalRev s (sfromK c) d
          _ -> s
        Nothing -> error "evalRev: tensor kinds don't match"
    (STKS shy yx, STKR nx@SNat zx) | Dict <- lemTensorKindOfAD yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) nx) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          evalRev s (sfromR c) d
        _ -> error "evalRev: tensor kinds don't match"
    (STKS shy yx, STKX shx zx) | Dict <- lemTensorKindOfAD yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) (ssxRank shx)) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          withKnownShX shx $
          evalRev s (sfromX c) d
        _ -> error "evalRev: tensor kinds don't match"
    (STKProduct @y1 @y2 stky1 stky2, STKProduct @z1 @z2 stkz1 stkz2)
      | Dict <- lemTensorKindOfSTK stky1
      , Dict <- lemTensorKindOfSTK stky2
      , Dict <- lemTensorKindOfSTK stkz1
      , Dict <- lemTensorKindOfSTK stkz2
      , Dict <- lemTensorKindOfAD stkz1
      , Dict <- lemTensorKindOfAD stkz2 ->
        let (c1, c2) = tunpair c
        in evalRev (evalRev s c1 (DeltaFromS @y1 @z1 $ DeltaProject1 d))
                   c2 (DeltaFromS @y2 @z2 $ DeltaProject2 d)
             -- TODO: costly
    _ -> error "evalRev: wrong tensor kinds"

  _ | Dict <- lemTensorKindOfAD (stensorKind @y) ->
      case sameTensorKind @y @(ADTensorKind y) of
        Just Refl -> evalRevSame s c d0
        _ -> s  -- the constructors remaining here have y that is a non-TKProduct
                -- so if y is equal to ADTensorKind y, the latter has
                -- the () scalar type and so no influence on the derivative.

evalRevSame
  :: forall y target.
     ( TensorKind y, ADReadyNoLet target, ShareTensor target
     , y ~ ADTensorKind y )
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalRevSame !s !c = \case
  -- All constructors that only admit a non-TKProduct kind
  -- (and the DeltaInput constructor and the vector space constructors)
  -- can be handled here, where the extra
  -- constraint makes it easier.
  DeltaCast @r1 d ->
    evalRev s (toADTensorKindShared (stensorKind @(TKScalar r1))
               $ kcast c) d
  DeltaSFromK d -> evalRevSame s (kfromS c) d
  DeltaInput _ftk i ->
    let cs = repToM stensorKind c
    in s {iMap = DMap.adjust (addRepM cs) i
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

  DeltaIndexR d ix -> evalRevSame s (roneHot (takeShape $ shapeDelta d) c ix) d
  DeltaSum0R d ->
    evalRevSame s (rreplicate0N (shapeDelta d) c) d
  DeltaDot0R v vd ->
    evalRevSame s (v * rreplicate0N (rshape v) c) vd
      -- too slow: evalRevSame s (rmap0N (* (tscalar c)) v) vd
  DeltaScatterR _sh d f ->
    evalRevSame s (rgather (shapeDelta d) c f) d
  DeltaAppendR d e -> case rshape c of
    n :$: _ -> let cShared = tshare c
                   k = lengthDelta d
                   s2 = evalRevSame s (rslice 0 k cShared) d
               in evalRevSame s2 (rslice k (n - k) cShared) e
    ZSR -> error "evalRevSame: impossible pattern needlessly required"
  DeltaSliceR i n d -> case tftk (stensorKind @y) c of
    FTKR (n' :$: rest) x ->
      assert (n' == n `blame` (n', n)) $
      evalRevSame s
               (rconcat $ NonEmpty.fromList
                  [ constantTarget 0 (FTKR (i :$: rest) x)
                  , c
                  , constantTarget 0 (FTKR (lengthDelta d - i - n :$: rest) x) ])
               d
    FTKR ZSR _ -> error "evalRevSame: impossible pattern needlessly required"
  DeltaReverseR d -> evalRevSame s (rreverse c) d
  DeltaTransposeR perm d ->
    let permR = permRInverse perm
    in evalRevSame s (rtranspose permR c) d
  DeltaReshapeR _sh d ->
    evalRevSame s (rreshape (shapeDelta d) c) d
  DeltaGatherR _sh d f ->
    evalRevSame s (rscatter (shapeDelta d) c f) d
  DeltaCastR @r1 @_ @n d ->
    evalRevRuntimeSpecialized s (toADTensorKindShared (stensorKind @(TKR n r1))
                                 $ rcast c) d
  DeltaZipR d ->
    evalRevSame s (runzip c) d
  DeltaUnzipR d ->
    evalRevSame s (rzip c) d

  DeltaIndexS d ix -> evalRevSame s (soneHot c ix) d
  DeltaSum0S @_ @sh d | SNat <- shsProduct (knownShS @sh) ->
    evalRevSame s (sreplicate0N c) d
  DeltaDot0S @_ @sh v vd | SNat <- shsProduct (knownShS @sh) ->
    evalRevSame s (v * sreplicate0N c) vd
      -- too slow: evalRevSame s (smap0N (* (sscalar c)) v) vd
  DeltaScatterS @_ @_ @shm @shn @shp d f ->
    evalRevSame s (sgather @_ @_ @shm @shn @shp c f) d
  DeltaAppendS @_ @_ @m d e ->
    let cShared = tshare c
        s2 = evalRevSame s (sslice (Proxy @0) Proxy cShared) d
    in evalRevSame s2 (sslice (Proxy @m) Proxy cShared) e
  DeltaSliceS @_ @i d -> case tftk (stensorKind @y) c of
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
  DeltaGatherS @_ @_ @shm @shn @shp d f ->
    evalRevSame s (sscatter @_ @_ @shm @shn @shp c f) d
  DeltaCastS @r1 @_ @sh d ->
    evalSRuntimeSpecialized s (toADTensorKindShared (stensorKind @(TKS sh r1))
                               $ scast c) d
  DeltaZipS d ->
    evalRevSame s (sunzip c) d
  DeltaUnzipS d ->
    evalRevSame s (szip c) d

  DeltaIndexX @sh1 @sh2 d ix -> case shapeDeltaFull d of
    FTKX sh _ -> evalRevSame s (xoneHot (shxTakeSSX (Proxy @sh2) sh
                                                    (knownShX @sh1)) c ix) d
  DeltaSum0X d ->
    evalRevSame s (xreplicate0N (shapeDeltaX d) c) d
  DeltaDot0X v vd ->
    evalRevSame s (v * xreplicate0N (xshape v) c) vd
      -- too slow: evalRevSame s (smap0N (* (sscalar c)) v) vd
  DeltaScatterX @_ @_ @shm @shn @shp _sh d f ->
    evalRevSame s (xgather @_ @_ @shm @shn @shp (shapeDeltaX d) c f) d
  DeltaAppendX d e -> case (shapeDeltaX d, shapeDeltaX e) of
    (shd@(Nested.SUnknown m :$% rest), she@(Nested.SUnknown n :$% _)) ->
      withSNat m $ \(SNat @m) -> withSNat n $ \(SNat @n) ->
      let cShared =
            tshare $ xmcast (ssxFromShape
                             $ Nested.SKnown (SNat @(m + n)) :$% rest) c
          s2 = evalRevSame s (xmcast (ssxFromShape shd)
                              $ xslice (Proxy @0) (Proxy @m) cShared) d
      in evalRevSame s2 (xmcast (ssxFromShape she)
                         $ xslice (Proxy @m) (Proxy @n) cShared) e
  DeltaSliceX @_ @i @n @k d -> case tftk (stensorKind @y) c of
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
  DeltaReshapeX _sh d ->
    evalRevSame s (xreshape (shapeDeltaX d) c) d
  DeltaGatherX @_ @_ @shm @shn @shp _sh d f ->
    evalRevSame s (xscatter @_ @_ @shm @shn @shp (shapeDeltaX d) c f) d
  DeltaCastX @r1 @_ @sh d ->
    evalXRuntimeSpecialized s (toADTensorKindShared (stensorKind @(TKX sh r1))
                               $ xcast c) d
  DeltaZipX d ->
    evalRevSame s (xunzip c) d
  DeltaUnzipX d ->
    evalRevSame s (xzip c) d

  DeltaSFromR @sh @x (DeltaFromS @y2 d) -> case sameTensorKind @y2 @(TKS2 sh x) of
    Just Refl -> evalRevSame s c d
    _ -> error "evalRevSame: different shapes in DeltaSFromR(DeltaFromS)"
  DeltaSFromR d ->
    evalRevSame s (rfromS c) d
  DeltaSFromX @sh @_ @x (DeltaFromS @y2 d) -> case sameTensorKind @y2 @(TKS2 sh x) of
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
          s3 = case stensorKind @y of
            STKR @n SNat (STKScalar @r _) -> case DMap.lookup n dMap of
              Just (RepAD c) -> evalRevRuntimeSpecialized @n @r s2 c d
              Nothing -> errorMissing
            STKS @sh sh (STKScalar @r _) ->
              withKnownShS sh $ case DMap.lookup n dMap of
                Just (RepAD c) -> evalSRuntimeSpecialized @sh @r s2 c d
                Nothing -> errorMissing
            STKX @sh sh (STKScalar @r _) ->
              withKnownShX sh $ case DMap.lookup n dMap of
                Just (RepAD c) -> evalXRuntimeSpecialized @sh @r s2 c d
                Nothing -> errorMissing
            _ -> case DMap.lookup n dMap of
              Just (RepAD c) -> evalRev s2 c d
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
     (ADReadyNoLet target, ShareTensor target, TensorKind y)
  => IMap target -> ADMap target -> Delta target y
  -> (ADMap target, target (ADTensorKind y))
evalFwd params s d0 = case d0 of
  DeltaPair @y1 @y2 d1 d2 | Dict <- lemTensorKindOfAD (stensorKind @y1)
                      , Dict <- lemTensorKindOfAD (stensorKind @y2) ->
    let (s2, t) = evalFwd params s d1
        (s3, u) = evalFwd params s2 d2
    in (s3, tpair t u)
  DeltaProject1 @_ @z d | Dict <- lemTensorKindOfAD (stensorKind @y)
                    , Dict <- lemTensorKindOfAD (stensorKind @z) ->
    let (s2, v) = evalFwd params s d
    in (s2, tproject1 v)
  DeltaProject2 @x d | Dict <- lemTensorKindOfAD (stensorKind @y)
                 , Dict <- lemTensorKindOfAD (stensorKind @x) ->
    let (s2, v) = evalFwd params s d
    in (s2, tproject2 v)
  DeltaFromVector snat stk lsd | Refl <- lemBuildOfAD snat stk ->
    let (s2, l) = mapAccumL (evalFwd params) s lsd
    in (s2, tfromVectorShare snat (aDSTK stk) l)
  DeltaSum snat stk d | Refl <- lemBuildOfAD snat stk ->
    let (s2, t) = evalFwd params s d
    in (s2, tsumShare snat (aDSTK stk) t)
  DeltaReplicate snat stk d | Refl <- lemBuildOfAD snat stk ->
    let (s2, t) = evalFwd params s d
    in (s2, treplicateShare snat (aDSTK stk) t)
  DeltaInput _ftk inputId ->
    case DMap.lookup inputId params of
      Just dtk -> (s, toADTensorKindShared stensorKind $ evalRepM dtk)
      Nothing -> error "evalFwd: missing input"
  DeltaShare n d | Dict <- lemTensorKindOfAD (stensorKind @y) ->
    case DMap.lookup n s of
      Just e1 -> (s, unRepAD e1)
      Nothing ->
        let (s2, cRaw) = evalFwd params s d
            cShared = tshare cRaw
            cd = RepAD cShared
              -- cRaw is shared, because it's put into the map and then
              -- potentially looked up many times, so it'd get duplicated
            s3 = DMap.insert n cd s2
        in (s3, cShared)

  DeltaMapAccumR @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            df _rf acc0' es'
   | Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind accShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDFTK accShs
        bShsAD = aDFTK bShs
        eShsAD = aDFTK eShs
        (s2, cacc0) = evalFwd params s acc0'
        (s3, ces) = evalFwd params s2 es'
    in (s3, dmapAccumR (Proxy @target)
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
   | Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind accShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDFTK accShs
        bShsAD = aDFTK bShs
        eShsAD = aDFTK eShs
        (s2, cacc0) = evalFwd params s acc0'
        (s3, ces) = evalFwd params s2 es'
    in (s3, dmapAccumL (Proxy @target)
                       k accShsAD bShsAD (FTKProduct eShsAD
                                                     (FTKProduct accShs eShs))
                       (\dacc de_acc_e ->
                        tlet de_acc_e $ \ !de_acc_e1 ->
                          unHFun df (tpair (tpair dacc (tproject1 de_acc_e1))
                                           (tproject2 de_acc_e1)))
                       cacc0
                       (tpair ces (tpair q es)))
  DeltaFromS @_ @z (DeltaSFromR @sh @x d)
    | Just Refl <- sameSTK (aDSTK (stensorKind @z))
                           (aDSTK (stensorKind @(TKR2 (Rank sh) x))) ->
      evalFwd params s d
  DeltaFromS @_ @z (DeltaSFromX @_ @sh' @x d)
    | Just Refl <- sameSTK (aDSTK (stensorKind @z))
                           (aDSTK (stensorKind @(TKX2 sh' x))) ->
      evalFwd params s d
  DeltaFromS @y2 @z d | Dict <- lemTensorKindOfAD (stensorKind @y2)
                 , Dict <- lemTensorKindOfAD (stensorKind @z) ->
    second tfromSShare $ evalFwd params s d

  _ | Dict <- lemTensorKindOfAD (stensorKind @y) ->
      case sameTensorKind @y @(ADTensorKind y) of
        Just Refl -> evalFwdSame params s d0
        _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)

evalFwdSame
  :: forall target y.
     ( TensorKind y, ADReadyNoLet target, ShareTensor target
     , y ~ ADTensorKind y )
  => IMap target -> ADMap target -> Delta target y
  -> (ADMap target, target (ADTensorKind y))
evalFwdSame params s = \case
  d0@(DeltaCast @r1 d) ->
    case sameSTK (STKScalar (typeRep @r1)) (aDSTK (STKScalar (typeRep @r1))) of
      Just Refl -> second kcast $ evalFwdSame params s d
      _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)
  DeltaSFromK d -> let (s2, t) = evalFwdSame params s d
                   in (s2, sfromK t)
  DeltaInput _ftk inputId ->
    case DMap.lookup inputId params of
      Just dtk -> (s, evalRepM dtk)
      Nothing -> error "evalFwdSame: missing input"
  -- See the comment about these three in evalRevSame.
  DeltaZero ftk -> (s, constantTarget 0 $ aDFTK ftk)
  DeltaScale k d -> second (* k) $ evalFwdSame params s d
  DeltaAdd d e -> let (s2, t) = evalFwdSame params s d
                      (s3, u) = evalFwdSame params s2 e
                  in (s3, t + u)

  DeltaIndexR d ix -> second (`rindex` ix) $ evalFwdSame params s d
  DeltaSum0R (DeltaZero (FTKR _ x)) -> (s, constantTarget 0 (FTKR ZSR x))
  DeltaSum0R d -> second rsum0 $ evalFwdSame params s d
  DeltaDot0R _ DeltaZero{} -> (s, rscalar 0)
  DeltaDot0R v d -> second (rdot0 v) $ evalFwdSame params s d
  DeltaScatterR sh d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, rscatter sh t f)
  DeltaAppendR d e ->
    let (s2, t) = evalFwdSame params s d
        (s3, u) = evalFwdSame params s2 e
    in (s3, rappend t u)
  DeltaSliceR i n d -> second (rslice i n) $ evalFwdSame params s d
  DeltaReverseR d -> second rreverse $ evalFwdSame params s d
  DeltaTransposeR perm d -> second (rtranspose perm) $ evalFwdSame params s d
  DeltaReshapeR sh d -> second (rreshape sh) $ evalFwdSame params s d
  DeltaGatherR sh d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, rgather sh t f)
  d0@(DeltaCastR @r1 @_ @n d) ->
    case sameSTK (stensorKind @(TKR n r1))
                 (aDSTK ((stensorKind @(TKR n r1)))) of
      Just Refl -> second rcast $ evalFwdSame params s d
      _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)
  DeltaZipR d -> second rzip $ evalFwdSame params s d
  DeltaUnzipR d -> second runzip $ evalFwdSame params s d
-- Not needed, because we take only the i-th component of the vector,
-- so v is not copied.
--  in (s2, rfromD $ tunvector v) V.! i)

  DeltaIndexS d ix -> second (`sindex` ix) $ evalFwdSame params s d
  DeltaSum0S (DeltaZero (FTKS _ x)) -> (s, constantTarget 0 (FTKS ZSS x))
  DeltaSum0S d -> second ssum0 $ evalFwdSame params s d
  DeltaDot0S _ DeltaZero{} -> (s, srepl 0)
  DeltaDot0S v d -> second (sdot0 v) $ evalFwdSame params s d
  DeltaScatterS @_ @_ @shm @shn @shp d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, sscatter @_ @_ @shm @shn @shp t f)
  DeltaAppendS d e ->
    let (s2, t) = evalFwdSame params s d
        (s3, u) = evalFwdSame params s2 e
    in (s3, sappend t u)
  DeltaSliceS @_ @i d -> second (sslice (Proxy @i) Proxy) $ evalFwdSame params s d
  DeltaReverseS d -> second sreverse $ evalFwdSame params s d
  DeltaTransposeS perm d -> second (stranspose perm)
                       $ evalFwdSame params s d
  DeltaReshapeS d -> second sreshape $ evalFwdSame params s d
  DeltaGatherS @_ @_ @shm @shn @shp d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, sgather @_ @_ @shm @shn @shp t f)
  d0@(DeltaCastS @r1 @_ @sh d) ->
    case sameSTK (stensorKind @(TKS sh r1))
                 (aDSTK ((stensorKind @(TKS sh r1)))) of
      Just Refl -> second scast $ evalFwdSame params s d
      _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)
  DeltaZipS d -> second szip $ evalFwdSame params s d
  DeltaUnzipS d -> second sunzip $ evalFwdSame params s d
-- Not needed, because we take only the i-th component of the vector,
-- so v is not copied.
--  in (s2, sfromD $ tunvector v V.! i)

  DeltaIndexX d ix -> second (`xindex` ix) $ evalFwdSame params s d
  DeltaSum0X (DeltaZero (FTKX _ x)) -> (s, constantTarget 0 (FTKX ZSX x))
  DeltaSum0X d -> second xsum0 $ evalFwdSame params s d
  DeltaDot0X _ DeltaZero{} -> (s, xrepl ZSX 0)
  DeltaDot0X v d -> second (xdot0 v) $ evalFwdSame params s d
  DeltaScatterX @_ @_ @shm @shn @shp sh d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, xscatter @_ @_ @shm @shn @shp sh t f)
  DeltaAppendX d e ->
    let (s2, t) = evalFwdSame params s d
        (s3, u) = evalFwdSame params s2 e
    in (s3, xappend t u)
  DeltaSliceX @_ @i d -> second (xslice (Proxy @i) Proxy) $ evalFwdSame params s d
  DeltaReverseX d -> second xreverse $ evalFwdSame params s d
  DeltaTransposeX perm d -> second (xtranspose perm)
                       $ evalFwdSame params s d
  DeltaReshapeX sh2 d -> second (xreshape sh2) $ evalFwdSame params s d
  DeltaGatherX @_ @_ @shm @shn @shp sh d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, xgather @_ @_ @shm @shn @shp sh t f)
  d0@(DeltaCastX @r1 @_ @sh d) ->
    case sameSTK (stensorKind @(TKX sh r1))
                 (aDSTK ((stensorKind @(TKX sh r1)))) of
      Just Refl -> second xcast $ evalFwdSame params s d
      _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)
  DeltaZipX d -> second xzip $ evalFwdSame params s d
  DeltaUnzipX d -> second xunzip $ evalFwdSame params s d

  DeltaSFromR @sh @x (DeltaFromS @y2 d) -> case sameTensorKind @y2 @(TKS2 sh x) of
    Just Refl -> evalFwdSame params s d
    _ -> error "evalFwdSame: different shapes in DeltaSFromR(DeltaFromS)"
  DeltaSFromR d -> second sfromR $ evalFwdSame params s d
  DeltaSFromX @sh @_ @x (DeltaFromS @y2 d) -> case sameTensorKind @y2 @(TKS2 sh x) of
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
