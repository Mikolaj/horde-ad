{-# LANGUAGE CPP, DataKinds, DeriveAnyClass, DeriveGeneric, DerivingStrategies,
             GADTs, GeneralizedNewtypeDeriving, KindSignatures, RankNTypes,
             StandaloneDeriving, UnboxedTuples #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The second component of our rendition of dual numbers:
-- delta expressions, with their semantics.
-- Neel Krishnaswami calls them \"sparse vector expressions\",
-- and indeed even in the simplest case of an objective function
-- defined on scalars only, the codomain of the function that computes
-- gradients from such delta expressions is a set of vectors, because
-- the gradient of an @R^n@ to @R@ function is an @R^n@ vector.
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
-- This is an internal low-level API, while the module @DualClass@
-- is an intermediate mid-level API that generates 'NodeId' identifiers
-- and provides a generalization to other kinds of second components
-- of dual numbers, e.g., the same as primal component for fast computation
-- of forward derivatives (because @derivativeFromDelta@ below,
-- computing derivatives from delta-expressions, is slow once
-- the expressions grow large enough to affect cache misses).
--
-- This simplified rendering of the library now contains two ranks:
-- scalars and (ranked) tensors. However, most haddocks and code comments
-- are unchanged since the times vectors were available instead of tensors.
-- The newer setting is a straightforward generalization of the older one,
-- so the rewritten comments would be very similar and slightly harder
-- to understand.
module HordeAd.Internal.Delta
  ( -- * Abstract syntax trees of the delta expressions
    Delta0 (..), Delta1 (..), DeltaX (..)
  , -- * Delta expression identifiers
    NodeId(..), InputId, toInputId
  , -- * Evaluation of the delta expressions
    DeltaDt (..), Domain0, Domain1, Domains(..), nullDomains
  , gradientFromDelta, derivativeFromDelta
  ) where

import Prelude

import           Control.DeepSeq (NFData)
import           Control.Exception.Assert.Sugar
import           Control.Monad (liftM2)
import           Control.Monad.ST.Strict (ST, runST)
import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import qualified Data.EnumMap.Strict as EM
import           Data.Kind (Type)
import           Data.List (foldl', sort)
import           Data.List.Index (ifoldl')
import           Data.Primitive (Prim)
import           Data.STRef (newSTRef, readSTRef, writeSTRef)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.Generics (Generic)
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Text.Show.Functions ()
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.SizedIndex
import HordeAd.Internal.OrthotopeOrphanInstances (liftVR)
import HordeAd.Internal.TensorOps

-- * Abstract syntax trees of the delta expressions

-- | For each choice of the underlying scalar type @r@,
-- we have several primitive differentiable types based on the scalar:
-- the scalar type @r@ itself, @Vector r@ and (in the non-simplified
-- version of delta expressions) @Matrix r@ and tensors.
-- Many operations span the ranks and so span the datatypes, which makes
-- the datatypes mutually recursive. Later on in this module,
-- algorithms are implemented for computing gradients and for computing
-- derivatives of objective functions from which such delta expressions
-- are obtained via our dual number method.
--
-- The first pair of grammars given below are of delta-expressions
-- at tensor rank 0, that is, at the scalar level. The first few operations
-- have analogues at the level of vectors, matrices and arbitrary tensors,
-- but the other operations are specific to the rank.
--
-- The `NodeId` identifier that appears in a @Let0 n d@ expression
-- is the unique identity stamp of subterm @d@, that is, there is
-- no different term @e@ such that @Let0 n e@ appears in any delta
-- expression term in memory during the same run of an executable.
-- The subterm identity is used to avoid evaluating shared
-- subterms repeatedly in gradient and derivative computations.
-- The identifier also represents data dependencies among terms
-- for the purpose of gradient and derivative computation. Computation for
-- a term may depend only on data obtained from terms with lower value
-- of their node identifiers. Such data dependency determination
-- agrees with the subterm relation, but is faster than traversing
-- the term tree in order to determine the relation of terms.
-- There is one exception to the subterm data dependency rule:
-- any term containing a function (e.g., a @Build1@ node)
-- may depend on terms generated by applying the function,
-- regardless of their node identifiers (which in our implementation
-- are going to be larger than their ancestors').
--
-- When computing gradients, node identifiers are also used to index,
-- directly or indirectly, the data accumulated for each node,
-- in the form of cotangents, that is partial derivatives
-- of the objective function with respect to the position(s)
-- of the node in the whole objective function dual number term
-- (or, more precisely, with respect to the single node in the term DAG,
-- in which subterms with the same node identifier are collapsed).
-- Only the @Input@ nodes of all ranks have a separate data storage.
-- The per-rank `InputId` identifiers in the @Input@ term constructors
-- are indexes into contiguous vectors of cotangents of exclusively @Input@
-- subterms of the whole term. The value at that index is the partial
-- derivative of the objective function (represented by the whole term,
-- or more precisely by (the data flow graph of) its particular
-- evaluation from which the delta expression originates)
-- with respect to the input parameter component at that index
-- in the objective function domain. The collection of all such
-- vectors of partial derivatives across all ranks is the gradient.
data Delta0 :: Type -> Type where
  Zero0 :: Delta0 r
  Input0 :: InputId r -> Delta0 r
  Scale0 :: r -> Delta0 r -> Delta0 r
  Add0 :: Delta0 r -> Delta0 r -> Delta0 r
  Let0 :: NodeId -> Delta0 r -> Delta0 r

  Index0 :: KnownNat n
         => Delta1 n r -> IndexInt n -> ShapeInt n -> Delta0 r
  Sum0 :: KnownNat n
       => ShapeInt n -> Delta1 n r -> Delta0 r
  Dot0 :: KnownNat n
       => OR.Array n r -> Delta1 n r -> Delta0 r
  UnScalar0 :: Delta1 0 r -> Delta0 r

deriving instance (Show r, Numeric r) => Show (Delta0 r)

-- | This is the grammar of delta-expressions at arbitrary tensor rank.
-- The comments refer to the ordinary (forward) semantics of the terms,
-- as given in @buildDerivative@. Evaluating the terms backwards
-- (transposing) to compute gradients provides a different semantics.
data Delta1 :: Nat -> Type -> Type where
  Zero1 :: Delta1 n r
  -- Input1  -- never used
  Scale1 :: OR.Array n r -> Delta1 n r -> Delta1 n r
  Add1 :: Delta1 n r -> Delta1 n r -> Delta1 n r
  Let1 :: NodeId -> Delta1 n r -> Delta1 n r

  Index1 :: KnownNat n
         => Delta1 (1 + n) r -> Int -> Int -> Delta1 n r
    -- ^ The sub-tensors at the given index of the outermost dimension.
    -- The second integer is the length of the dimension.
  IndexN :: (KnownNat n, KnownNat m)
         => Delta1 (m + n) r -> IndexInt m -> ShapeInt (m + n) -> Delta1 n r
    -- ^ The sub-tensor at the given index. The given shape is of the
    -- large tensor. The operation fails if index is out of bounds.
  Sum1 :: KnownNat n
       => Int -> Delta1 (1 + n) r -> Delta1 n r
    -- ^ Add element tensors along the outermost dimension.
  Scalar1 :: Delta0 r -> Delta1 0 r
    -- ^ Conversion between rank 0 and 1 (ranked tensors).
  FromList1 :: KnownNat n
            => [Delta1 n r] -> Delta1 (1 + n) r
    -- ^ Create a tensor from a list treated as the outermost dimension.
  FromVector1 :: KnownNat n
              => Data.Vector.Vector (Delta1 n r)
              -> Delta1 (1 + n) r
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  FromList01 :: ShapeInt n -> [Delta0 r] -> Delta1 n r
  FromVector01 :: ShapeInt n -> Data.Vector.Vector (Delta0 r) -> Delta1 n r
  Konst1 :: KnownNat n
         => Int -> Delta1 n r -> Delta1 (1 + n) r
    -- ^ Copy the given tensor along the new, outermost dimension.
  Konst01 :: ShapeInt n -> Delta0 r -> Delta1 n r
  Append1 :: KnownNat n
          => Delta1 n r -> Int -> Delta1 n r -> Delta1 n r
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
    -- The integer argument is the outermost size of the first array.
  Slice1 :: KnownNat n
         => Int -> Int -> Delta1 n r -> Int -> Delta1 n r
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
    -- The last argument is the outermost size of the argument array.
  Reverse1 :: KnownNat n
           => Delta1 (1 + n) r -> Delta1 (1 + n) r
    -- ^ Reverse elements of the outermost dimension.
  Transpose1 :: KnownNat n
             => Permutation -> Delta1 n r -> Delta1 n r
    -- ^ Transpose according to the permutation.
  Reshape1 :: (KnownNat n, KnownNat m)
           => ShapeInt n -> ShapeInt m -> Delta1 n r -> Delta1 m r
    -- ^ Change the shape of the tensor from the first to the second.
  Build1 :: KnownNat n
         => Int -> (Int -> Delta1 n r) -> Delta1 (1 + n) r
    -- ^ Build a tensor with the given size of the outermost dimension
    -- and using the given function to construct the element tensors.
  Build01 :: ShapeInt n -> (IndexInt n -> Delta0 r) -> Delta1 n r
  Gather1 :: (KnownNat p, KnownNat n)
          => (Int -> IndexInt p)
          -> ShapeInt (p + n) -> Delta1 (p + n) r
          -> Int -> Delta1 (1 + n) r
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @Gather1 (const Z) [] (Scalar1 d) k@ is equivalent
    -- to @Konst01 [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @GatherN@).
  GatherN :: (KnownNat m, KnownNat p, KnownNat n)
          => (IndexInt m -> IndexInt p)
          -> ShapeInt (p + n) -> Delta1 (p + n) r
          -> ShapeInt (m + n) -> Delta1 (m + n) r
  Scatter1 :: (KnownNat p, KnownNat n)
           => (Int -> IndexInt p)
           -> Int -> Delta1 (1 + n) r
           -> ShapeInt (p + n) -> Delta1 (p + n) r
    -- ^ Build a tensor by adding up tensors of rank @n@ taken from
    -- the third argument and inserted in a zero tensor
    -- at indexes of length @p@. Indexes of length 0 insert tensors trivially,
    -- so that, e.g, @Scatter1 5 (const Z) (Konst01 [5] d) []@ is equivalent
    -- to @5 * d@. If an index of length @p@ is out of bounds, no tensor
    -- is added at such an index (and similarly in @ScatterN@).
  ScatterN :: (KnownNat m, KnownNat p, KnownNat n)
           => (IndexInt m -> IndexInt p)
           -> ShapeInt (m + n) -> Delta1 (m + n) r
           -> ShapeInt (p + n) -> Delta1 (p + n) r

  FromX1 :: DeltaX r -> Delta1 n r

deriving instance (Show r, Numeric r) => Show (Delta1 n r)

data DeltaX :: Type -> Type where
  InputX :: InputId (OT.Array r) -> DeltaX r
  From1X :: Delta1 n r -> DeltaX r

deriving instance (Show r, Numeric r) => Show (DeltaX r)

-- * Delta expression identifiers

newtype NodeId = NodeId {fromNodeId :: Int}
  deriving newtype (Enum, Prim)
    -- The Prim instance conversions take lots of time when old-time profiling,
    -- but are completely optimized away in normal builds.
    -- No Eq instance to limit hacks outside this module.

instance Show NodeId where
  show (NodeId n) = show n  -- to keep debug printouts readable

newtype InputId a = InputId Int
  deriving (Show, Enum)
    -- No Eq instance to limit hacks outside this module.

-- | Wrap non-negative (only!) integers in the `InputId` newtype.
toInputId :: Int -> InputId a
toInputId i = assert (i >= 0) $ InputId i


-- * Evaluation of the delta expressions

-- | Helper definitions to shorten type signatures. @Domains@, among other
-- roles, is the internal representation of domains of objective functions.
type Domain0 r = Vector r

-- To store shaped tensor we use untyped tensors instead of vectors
-- to prevent frequent linearization of tensors (e.g., after transpose).
type Domain1 r = Data.Vector.Vector (OT.Array r)

data Domains r = Domains
  { domains0 :: Domain0 r
  , domains1 :: Domain1 r
  }
  deriving (Show, Generic, NFData)

nullDomains :: Numeric r => Domains r -> Bool
nullDomains Domains{..} =
  V.null domains0 && V.null domains1

-- | The main input of the differentiation functions:
-- the delta expression to be differentiated and the dt perturbation
-- (small change) of the objective function codomain, for which we compute
-- the gradient.
data DeltaDt r =
    DeltaDt0 r (Delta0 r)
  | forall n. KnownNat n
    => DeltaDt1 (OR.Array n r) (Delta1 n r)

-- | The state of evaluation. It consists of several maps.
-- The maps indexed by input identifiers and node identifiers
-- eventually store cotangents for their respective nodes.
-- The cotangents are built gradually during the evaluation,
-- by summing cotangent contributions.
--
-- Data invariant:
-- 1. keys dMap0 `intersect` keys dMap1 == mempty
-- 2. keys nMap == keys dMap0 `union` keys dMap1
-- 3. key `member` dMap0 == nMap!key is DeltaBinding0
-- 4. key `member` dMap1 == nMap!key is DeltaBinding1
data EvalState r = EvalState
  { iMap0 :: EM.EnumMap (InputId r) r
      -- ^ eventually, cotangents of objective function inputs of rank 0
      -- (finally copied to the vector representing the rank 0 portion
      -- of the gradient of the objective function);
      -- the identifiers need to be contiguous and start at 0
  , iMap1 :: EM.EnumMap (InputId (OT.Array r)) (OT.Array r)
      -- ^ eventually, cotangents of objective function inputs of rank 1;
      -- (eventually copied to the vector representing the rank 1 portion
      -- of the gradient of the objective function);
      -- the identifiers need to be contiguous and start at 0
  , dMap0 :: EM.EnumMap NodeId r
      -- ^ eventually, cotangents of non-input subterms of rank 0 indexed
      -- by their node identifiers
  , dMap1 :: EM.EnumMap NodeId (OT.Array r)
      -- ^ eventually, cotangents of non-input subterms of rank 1 indexed
      -- by their node identifiers
  , nMap  :: EM.EnumMap NodeId (DeltaBinding r)
      -- ^ nodes left to be evaluated
  }

-- | Nodes left to be evaluated.
-- We can't evaluate them at once, because their other shared copies
-- may still not be processed, so we'd not take advantage of the sharing
-- and not take into account the whole summed context when finally evaluating.
data DeltaBinding r =
    DeltaBinding0 (Delta0 r)
  | forall n. KnownNat n
    => DeltaBinding1 (Delta1 n r)

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
-- of finite maps or vectors) of type @Domains r@ and produces
-- a single result of type @r@. Let a dual number counterpart
-- of @f@ applied to a fixed collection of parameters @P@
-- of type @Domains r@ be represented as a Haskell value @b@.
-- Let @d :: Delta0 r@ be the delta expression that is
-- the second component of @b@, let @ds@ belong to @Domains r@.
-- The semantics of @d@ is a linear function from @Domains r@
-- to @r@ that is the derivative of @f@ at point @P@
-- with respect to the perturbation @ds@. The mathematical formula
-- for the derivative follows straightforwardly the syntactic form
-- of the delta expression @d@ (see 'derivativeFromDelta').
--
-- Let's now describe the semantics of a delta expression @d@
-- as the gradient of @f@ at point @P@ with respect to a @dt@ that belongs
-- to @r@. Here the semantics of @d@ is a collection of finite maps
-- (vectors) @v0@, @v1@, ..., corresponding to @Domains r@.
-- The value of @vi@ at index @k@ is the partial derivative
-- of function @f@ at @P@ with respect to its parameter of type @ai@
-- residing at index @k@.
--
-- Function @gradientFromDelta@ computes the four vectors described above.
-- Requested lengths of the vectors are given in the first few arguments.
-- The delta expression to be evaluated, together with the @dt@ perturbation
-- value (usually set to @1@) is given in the @DeltaDt r@ parameter.
gradientFromDelta
  :: forall r. (Numeric r, Show r, Num (Vector r))
  => Int -> Int -> DeltaDt r
  -> Domains r
gradientFromDelta dim0 dim1 deltaDt =
  -- Create finite maps that hold values associated with inputs
  -- and with (possibly shared) term tree nodes.
  -- The former are initialized with dummy values so that it's cheap
  -- to check if any update has already been performed to a cell
  -- (allocating big vectors filled with zeros is too costly,
  -- especially if never used in an iteration, and adding to such vectors
  -- and especially using them as cotangent accumulators is wasteful;
  -- additionally, it may not be easy to deduce the sizes of the vectors).
  let s0 =
        let iMap0 = EM.fromDistinctAscList
                    $ zip [toInputId 0 ..]
                          (replicate dim0 0)
                      -- 0 is the correct value; below is a dummy value
            iMap1 = EM.fromDistinctAscList
                    $ zip [toInputId 0 ..]
                          (replicate dim1 (dummyTensor :: OT.Array r))
            dMap0 = EM.empty
            dMap1 = EM.empty
            nMap = EM.empty
        in EvalState {..}

  -- Eval.
  in let EvalState{iMap0, iMap1} = buildFinMaps s0 deltaDt

  -- Extract results.
  in Domains (V.fromList $ EM.elems iMap0) (V.fromList $ EM.elems iMap1)
{-# SPECIALIZE gradientFromDelta
  :: Int -> Int -> DeltaDt Double -> Domains Double #-}

buildFinMaps :: forall r. (Numeric r, Show r, Num (Vector r))
             => EvalState r -> DeltaDt r -> EvalState r
buildFinMaps s0 deltaDt =
  -- The first argument is the evaluation state being modified,
  -- the second is the cotangent accumulator that will become an actual
  -- cotangent contribution when complete (see below for an explanation)
  -- and the third argument is the node to evaluate.
  let eval0 :: EvalState r -> r -> Delta0 r -> EvalState r
      eval0 s !c = \case
        Zero0 -> s
        Input0 i -> s {iMap0 = EM.adjust (+ c) i $ iMap0 s}
        Scale0 k d -> eval0 s (k * c) d
        Add0 d e -> eval0 (eval0 s c d) c e
        Let0 n d ->
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
          -- corresponding to the shared term @Let0 n d@. This total
          -- influence over the objective function's behaviour is called
          -- in short the cotangent of the node identifier @n@.
          -- In other words, the cotangent of @n@ is the sum,
          -- over all positions (edges) q in the global delta-expression DAG
          -- that are a reference to node @n@, of the partial derivative
          -- of the objective function with respect to the subcomputation
          -- corresponding to @q@ (meaning, subcomputations denoted by
          -- Haskell terms whose dual components are @Let n ...@).
          --
          -- For @Input@ terms, the eventual lists of cotangents end up
          -- in the cells of the gradient vectors that are the final
          -- result of the evaluation.
          assert (case d of
                    Zero0 -> False
                    Input0{} -> False
                    Let0{} -> False  -- wasteful and nonsensical
                    _ -> True)
          $ case EM.lookup n $ nMap s of
              Just (DeltaBinding0 _) ->
                s {dMap0 = EM.adjust (+ c) n $ dMap0 s}
              Nothing ->
                s { nMap = EM.insert n (DeltaBinding0 d) $ nMap s
                  , dMap0 = EM.insert n c $ dMap0 s }
              _ -> error "buildFinMaps: corrupted nMap"

        -- The general case is given as the last one below,
        -- but for a few constructors it's faster to inline @eval1@ instead.
        -- BTW, such an optimization doesn't really belong in the simplified
        -- horde-ad and no consistent benefit should be expected here.
        Index0 Zero1 _ _ -> s  -- shortcut
        Index0 (FromX1 (InputX i)) ixs' sh ->
          let ixs = indexToList ixs'
              f v = if isTensorDummy v
                    then OT.constant (shapeToList sh) 0 `OT.update` [(ixs, c)]
                    else v `OT.update` [(ixs, v `tindex0D` ixs + c)]
          in s {iMap1 = EM.adjust f i $ iMap1 s}
        Index0 (Let1 n d) ixs' sh ->
          let ixs = indexToList ixs'
          in case EM.lookup n $ nMap s of
            Just (DeltaBinding1 _) ->
              let f v = v `OT.update` [(ixs, v `tindex0D` ixs + c)]
              in s {dMap1 = EM.adjust f n $ dMap1 s}
                -- This would be an asymptotic optimization compared to
                -- the general case below, if not for the non-mutable update,
                -- which implies copying the whole @v@ vector,
                -- so it's only several times faster (same allocation,
                -- but not adding to each cell of @v@).
            Nothing ->
              let v = OT.constant (shapeToList sh) 0 `OT.update` [(ixs, c)]
              in s { nMap = EM.insert n (DeltaBinding1 d) $ nMap s
                   , dMap1 = EM.insert n v $ dMap1 s }
            _ -> error "buildFinMaps: corrupted nMap"
        Index0 d ixs sh -> eval1 s (tkonst0NR sh 0 `updateR` [(ixs, c)]) d
        Sum0 sh d -> eval1 s (tkonst0NR sh c) d
        Dot0 v vd -> eval1 s (liftVR (LA.scale c) v) vd
        UnScalar0 d -> eval1 s (OR.scalar c) d

      addToArray :: OR.Array n r -> OT.Array r -> OT.Array r
      addToArray c = \v -> let cs = Data.Array.Convert.convert c
                           in if isTensorDummy v
                              then cs
                              else v + cs
      eval1 :: KnownNat n
            => EvalState r -> OR.Array n r -> Delta1 n r -> EvalState r
      eval1 s !c = \case
        Zero1 -> s
        Scale1 k d -> eval1 s (k * c) d
        Add1 d e -> eval1 (eval1 s c d) c e
        Let1 n d ->
          assert (case d of
                    Zero1 -> False
                    FromX1{} -> False
                    Let1{} -> False  -- wasteful and nonsensical
                    _ -> True)
          $ case EM.lookup n $ nMap s of
              Just (DeltaBinding1 _) ->
                let cs = Data.Array.Convert.convert c
                in s {dMap1 = EM.adjust (+ cs) n $ dMap1 s}
              Nothing ->
                let cs = Data.Array.Convert.convert c
                in s { nMap = EM.insert n (DeltaBinding1 d) $ nMap s
                     , dMap1 = EM.insert n cs $ dMap1 s }
              _ -> error "buildFinMaps: corrupted nMap"

        Index1 d ix len ->
          let rest = OR.shapeL c
          in eval1 s (OR.concatOuter [ OR.constant (ix : rest) 0
                                     , OR.reshape (1 : rest) c
                                     , OR.constant (len - ix - 1 : rest) 0 ])
                     d  -- TODO: optimize for input case
        IndexN d ixs sh -> eval1 s (updateNR (tkonst0NR sh 0) [(ixs, c)]) d
        Sum1 n d -> eval1 s (OR.ravel (ORB.constant [n] c)) d
        Scalar1 d -> eval0 s (OR.unScalar c) d
        FromList1 ld ->
          let lc = ORB.toList $ OR.unravel c
          in foldl' (\s2 (c2, d2) -> eval1 s2 c2 d2) s $ zip lc ld
        FromVector1 ld ->
          let lc = ORB.toList $ OR.unravel c
          in foldl' (\s2 (c2, d2) -> eval1 s2 c2 d2) s $ zip lc (V.toList ld)
        FromList01 _sh lsd ->  -- lsd is a list of scalar delta expressions
          let cv = OR.toVector c
          in ifoldl' (\s2 i d -> eval0 s2 (cv V.! i) d) s lsd
        FromVector01 _sh lsd ->  -- lsd is a list of scalar delta expressions
          let cv = OR.toVector c
          in V.ifoldl' (\s2 i d -> eval0 s2 (cv V.! i) d) s lsd
        Konst1 _n d ->
          let c2 = V.sum $ ORB.toVector $ OR.unravel c
              -- simplified version of: tscatter1R (const []) c (tail $ shapeL c)
          in eval1 s c2 d
        Konst01 _ d -> eval0 s (tsum0R c) d
        Append1 d k e -> case OR.shapeL c of
          n : _ -> let s2 = eval1 s (OR.slice [(0, k)] c) d
                   in eval1 s2 (OR.slice [(k, n - k)] c) e
          [] -> error "eval1: appending a 0-dimensional tensor"
        Slice1 i n d len -> case OR.shapeL c of
          n' : rest ->
            assert (n' == n `blame` (n', n)) $
            eval1 s (OR.concatOuter [ OR.constant (i : rest) 0
                                    , c
                                    , OR.constant (len - i - n : rest) 0 ])
                    d
          [] -> error "eval1: slicing a 0-dimensional tensor"
        Reverse1 d -> eval1 s (treverseR c) d
        Transpose1 perm d ->
          let perm_reversed = map snd $ sort $ zip perm [0 .. length perm - 1]
          in eval1 s (ttransposeR perm_reversed c) d
        Reshape1 sh _sh' d -> eval1 s (treshapeR sh c) d
        Build1 _n f -> V.ifoldl' (\s2 i ci -> eval1 s2 ci (f i))
                                 s (ORB.toVector $ OR.unravel c)
        Build01 sh f ->
          V.ifoldl' (\s2 i ci -> eval0 s2 ci (f $ fromLinearIdx sh i))
                    s (OR.toVector c)
        Gather1 f sh d _n -> eval1 s (tscatter1R f c sh) d
        GatherN f shd d _sh -> eval1 s (tscatterNR f c shd) d
        Scatter1 f n d _sh -> eval1 s (tgather1R n c f) d
        ScatterN f shd d _sh -> eval1 s (tgatherNR shd c f) d

        FromX1 (InputX inputId) ->
          s {iMap1 = EM.adjust (addToArray c) inputId $ iMap1 s}
        FromX1 (From1X d) -> eval1 s c (unsafeCoerce d)
          -- TODO: add a runtime check

      evalFromnMap :: EvalState r -> EvalState r
      evalFromnMap s@EvalState{nMap, dMap0, dMap1} =
        case EM.maxViewWithKey nMap of
          Just ((n, b), nMap2) ->
            let s2 = s {nMap = nMap2}
                s3 = case b of
                  DeltaBinding0 d -> let c = dMap0 EM.! n
                                     in eval0 s2 c d
                  DeltaBinding1 d -> let c = Data.Array.Convert.convert
                                             $ dMap1 EM.! n
                                     in eval1 s2 c d
            in evalFromnMap s3
          Nothing -> s  -- loop ends

      s1 = case deltaDt of
        DeltaDt0 dt deltaTopLevel -> eval0 s0 dt deltaTopLevel
        DeltaDt1 dt deltaTopLevel -> eval1 s0 dt deltaTopLevel
  in evalFromnMap s1

{-# SPECIALIZE buildFinMaps
  :: EvalState Double -> DeltaDt Double -> EvalState Double #-}

-- Unlike @buildFinMaps@, the following is simpler written in ST
-- than with explicit passing of state, because changing the state here
-- is really an irritating side effect, while in @buildFinMaps@ it's building
-- the result. Perhaps this can be simplified completely differently.

-- | Forward derivative computation via forward-evaluation of delta-expressions
-- (which is surprisingly competitive to the direct forward method,
-- until the allocation of deltas gets large enough to affect cache hits).
-- This is the directional derivative, calculated for the point,
-- at which the delta expression was computed (which is the point
-- represented by the parameters of the objective function and used
-- to compute it's dual number result) and along the direction vector(s)
-- given in the last parameter called @ds@.
derivativeFromDelta
  :: (Numeric r, Show r, Num (Vector r))
  => Int -> Int -> Delta0 r -> Domains r -> r
derivativeFromDelta dim0 dim1 deltaTopLevel ds =
  runST $ buildDerivative dim0 dim1 deltaTopLevel ds

-- | This mimics 'buildFinMaps', but in reverse. Perhaps this can be
-- simplified, but the obvious simplest formulation does not honour sharing
-- and evaluates shared subexpressions repeatedly.
buildDerivative
  :: forall s r. (Numeric r, Show r, Num (Vector r))
  => Int -> Int -> Delta0 r -> Domains r
  -> ST s r
buildDerivative dim0 dim1 deltaTopLevel
                Domains{..} = do
  dMap0 <- newSTRef EM.empty
  dMap1 <- newSTRef EM.empty
  nMap <- newSTRef EM.empty
  let eval0 :: Delta0 r -> ST s r
      eval0 = \case
        Zero0 -> return 0
        Input0 (InputId i) ->
          if i < dim0
          then return $! domains0 V.! i
          else error "derivativeFromDelta.eval': wrong index for an input"
        Scale0 k d -> (k *) <$> eval0 d
        Add0 d e -> liftM2 (+) (eval0 d) (eval0 e)
        Let0 n d -> do
          -- This is too complex, but uses components already defined
          -- for initializeFinMaps and some of a similar code.
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBinding0 _) -> do
              dm <- readSTRef dMap0
              return $! dm EM.! n
            Nothing -> do
              c <- eval0 d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMap0
              writeSTRef nMap $! EM.insert n (DeltaBinding0 d) nmNew
              writeSTRef dMap0 $! EM.insert n c dm
              return c
            _ -> error "buildDerivative: corrupted nMap"

        Index0 d ixs _ -> (`tindex0R` ixs) <$> eval1 d
        Sum0 _ d -> tsum0R <$> eval1 d
        Dot0 v d -> tdot0R v <$> eval1 d
        UnScalar0 d -> OR.unScalar <$> eval1 d

      eval1 :: KnownNat n => Delta1 n r -> ST s (OR.Array n r)
      eval1 = \case
        Zero1 -> return 0
        Scale1 k d -> (k *) <$> eval1 d
        Add1 d e -> liftM2 (+) (eval1 d) (eval1 e)
        Let1 n d -> do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBinding1 _) -> do
              dm <- readSTRef dMap1
              return $! Data.Array.Convert.convert (dm EM.! n :: OT.Array r)
            Nothing -> do
              c <- eval1 d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMap1
              writeSTRef nMap $! EM.insert n (DeltaBinding1 d) nmNew
              writeSTRef dMap1 $! EM.insert n (Data.Array.Convert.convert c) dm
              return c
            _ -> error "buildDerivative: corrupted nMap"

        Index1 d ix _len -> (`tindex1R` ix) <$> eval1 d
        IndexN d ixs _len -> (`tindexNR` ixs) <$> eval1 d
        Sum1 _ d -> tsumR <$> eval1 d
        Scalar1 d -> OR.scalar <$> eval0 d
        FromList1 lsd -> do
          l <- mapM eval1 lsd
          return $! tfromListR l
        FromVector1 lsd -> do
          l <- V.mapM eval1 lsd
          return $! tfromVectorR l
        FromList01 sh lsd -> do
          l <- mapM eval0 lsd
          return $! tfromList0NR sh l
        FromVector01 sh lsd -> do
          l <- V.mapM eval0 lsd
          return $! tfromVector0NR sh l
        Konst1 n d -> do
          t <- eval1 d
          return $! tkonstR n t
        Konst01 sh d -> tkonst0NR sh <$> eval0 d
        Append1 d _k e -> liftM2 tappendR (eval1 d) (eval1 e)
        Slice1 i n d _len -> tsliceR i n <$> eval1 d
        Reverse1 d -> treverseR <$> eval1 d
        Transpose1 perm d -> ttransposeR perm <$> eval1 d
        Reshape1 _sh sh' d -> treshapeR sh' <$> eval1 d
        Build1 n f -> do
          l <- mapM (eval1 . f) [0 .. n - 1]
          return $! OR.ravel $ ORB.fromList [n] l
        Build01 sh' f -> do
          let sh = shapeToList sh'
              s = product sh
          l <- mapM (eval0 . f)
                    [fromLinearIdx sh' i | i <- [0 .. s - 1]]
          return $! OR.fromList sh l
        Gather1 f _sh d k -> do
          t <- eval1 d
          return $! tgather1R k t f
        GatherN f _shd d sh -> do
          t <- eval1 d
          return $! tgatherNR sh t f
        Scatter1 f _k d sh -> do
          t <- eval1 d
          return $! tscatter1R f t sh
        ScatterN f _shd d sh ->  do
          t <- eval1 d
          return $! tscatterNR f t sh

        FromX1 (InputX (InputId i)) ->
          if i < dim1
          then return $! Data.Array.Convert.convert $ domains1 V.! i
          else error "derivativeFromDelta.eval': wrong index for an input"
        FromX1 (From1X d) -> eval1 (unsafeCoerce d)
          -- TODO: add a runtime check

  eval0 deltaTopLevel
