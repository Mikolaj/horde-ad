{-# LANGUAGE AllowAmbiguousTypes, DerivingStrategies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The second component of our rendition of dual numbers:
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
module HordeAd.Core.Delta
  ( -- * Abstract syntax trees of the delta expressions
    DeltaS (..), DeltaR (..), DeltaD (..)
  , -- * Delta expression identifiers
    NodeId (..), InputId, toInputId, Dual
  , -- * Evaluation of the delta expressions
    DeltaDt (..)
  , gradientFromDelta
  , ForwardDerivative (..)
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (liftM2)
import           Control.Monad.ST.Strict (ST, runST)
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Kind (Type)
import           Data.List (foldl', sort)
import           Data.List.Index (ifoldl')
import           Data.Proxy (Proxy (Proxy))
import           Data.STRef (newSTRef, readSTRef, writeSTRef)
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           GHC.TypeLits (KnownNat, Nat, sameNat, type (+))
import           Text.Show.Functions ()

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorAst ()
import HordeAd.Core.TensorClass

-- * Abstract syntax trees of the delta expressions

newtype NodeId = NodeId Int
 deriving newtype (Show, Enum)
   -- No Eq instance to limit hacks.

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
-- any term containing a function (e.g., a @BuildR@ node)
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
data DeltaS :: (Type -> Nat -> Type) -> (Type -> [Nat] -> Type)
            -> Type -> [Nat] -> Type where
  LetS :: NodeId -> DeltaS ranked shaped r sh -> DeltaS ranked shaped r sh

deriving instance (Show r) => Show (DeltaS ranked shaped r sh)

-- | This is the grammar of delta-expressions at arbitrary tensor rank.
-- The comments refer to the ordinary (forward) semantics of the terms,
-- as given in @buildDerivative@. Evaluating the terms backwards
-- (transposing the represented linear map) in order to compute gradients
-- provides a different semantics.
data DeltaR :: (Type -> Nat -> Type) -> Type -> Nat -> Type where
  ZeroR :: DeltaR ranked r n
  InputR :: InputId (ranked r n) -> DeltaR ranked r n
  ScaleR :: Show (ranked r n)
         => ranked r n -> DeltaR ranked r n -> DeltaR ranked r n
  AddR :: DeltaR ranked r n -> DeltaR ranked r n -> DeltaR ranked r n
  LetR :: NodeId -> DeltaR ranked r n -> DeltaR ranked r n

    -- ^ The sub-tensors at the given index of the outermost dimension.
    -- The second integer is the length of the dimension.
  IndexR :: (KnownNat n, KnownNat m)
         => DeltaR ranked r (m + n) -> IndexOf (ranked r 0) m
         -> ShapeInt (m + n) -> DeltaR ranked r n
    -- ^ The sub-tensor at the given index. The given shape is of the
    -- large tensor. The operation fails if index is out of bounds.
    -- If index is out of bounds, the result is defined and is 0.
  SumR :: KnownNat n
       => Int -> DeltaR ranked r (1 + n) -> DeltaR ranked r n
    -- ^ Add element tensors along the outermost dimension.
  Sum0R :: KnownNat n
       => ShapeInt n -> DeltaR ranked r n -> DeltaR ranked r 0
  Dot0R :: (KnownNat n, Show (ranked r n))
       => ranked r n -> DeltaR ranked r n -> DeltaR ranked r 0
  ScatterR :: (KnownNat m, KnownNat p, KnownNat n)
           => ShapeInt (p + n) -> DeltaR ranked r (m + n)
           -> (IndexOf (ranked r 0) m -> IndexOf (ranked r 0) p)
           -> ShapeInt (m + n)
           -> DeltaR ranked r (p + n)
    -- ^ Build a tensor by adding up tensors of rank @n@ taken from
    -- the third argument and inserted in a zero tensor
    -- at indexes of length @p@. Indexes of length 0 insert tensors trivially,
    -- so that, e.g, @Scatter1 5 (const Z) (Replicate0R [5] d) []@ is equivalent
    -- to @5 * d@. If an index of length @p@ is out of bounds, no tensor
    -- is added at such an index (and similarly in @ScatterN@).
    -- The semantics of the operation permits index out of bounds
    -- and then no tensors is added at such an index.
    -- TODO: this is a haddock for Scatter1; fix.

  FromListR :: KnownNat n
            => [DeltaR ranked r n] -> DeltaR ranked r (1 + n)
    -- ^ Create a tensor from a list treated as the outermost dimension.
  FromVectorR :: KnownNat n
              => Data.Vector.Vector (DeltaR ranked r n)
              -> DeltaR ranked r (1 + n)
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  ReplicateR :: KnownNat n
         => Int -> DeltaR ranked r n -> DeltaR ranked r (1 + n)
    -- ^ Copy the given tensor along the new, outermost dimension.
  AppendR :: KnownNat n
          => DeltaR ranked r (1 + n) -> Int -> DeltaR ranked r (1 + n)
          -> DeltaR ranked r (1 + n)
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
    -- The integer argument is the outermost size of the first array.
  SliceR :: KnownNat n
         => Int -> Int -> DeltaR ranked r (1 + n) -> Int
         -> DeltaR ranked r (1 + n)
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
    -- The last argument is the outermost size of the argument array.
  ReverseR :: KnownNat n
           => DeltaR ranked r (1 + n) -> DeltaR ranked r (1 + n)
    -- ^ Reverse elements of the outermost dimension.
  TransposeR :: KnownNat n
             => Permutation -> DeltaR ranked r n -> DeltaR ranked r n
    -- ^ Transpose according to the permutation.
  ReshapeR :: (KnownNat n, KnownNat m)
           => ShapeInt n -> ShapeInt m -> DeltaR ranked r n -> DeltaR ranked r m
    -- ^ Change the shape of the tensor from the first to the second.
  BuildR :: KnownNat n
         => Int -> (IntOf (ranked r 0) -> DeltaR ranked r n)
         -> DeltaR ranked r (1 + n)
    -- ^ Build a tensor with the given size of the outermost dimension
    -- and using the given function to construct the element tensors.
  GatherR :: (KnownNat m, KnownNat p, KnownNat n)
          => ShapeInt (m + n) -> DeltaR ranked r (p + n)
          -> (IndexOf (ranked r 0) m -> IndexOf (ranked r 0) p)
          -> ShapeInt (p + n)
          -> DeltaR ranked r (m + n)
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @Gather1 (const Z) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @GatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for Gather1; fix.

  DToR :: forall ranked shaped n r. DeltaD ranked shaped r -> DeltaR ranked r n

deriving instance (Show (IntOf (ranked r 0)), Show r)
                  => Show (DeltaR ranked r n)

data DeltaD :: (Type -> Nat -> Type) -> (Type -> [Nat] -> Type)
            -> Type -> Type where
  RToD :: forall ranked shaped n r. KnownNat n
         => DeltaR ranked r n -> DeltaD ranked shaped r

deriving instance (Show (IntOf (ranked r 0)), Show r)
                  => Show (DeltaD ranked shaped r)


-- * Related datatypes and classes

newtype InputId a = InputId Int
 deriving (Show, Enum)
   -- No Eq instance to limit hacks outside this module.

-- | Wrap non-negative (only!) integers in the `InputId` newtype.
toInputId :: Int -> InputId a
toInputId i = assert (i >= 0) $ InputId i

-- | The type family that to each basic differentiable type
-- assigns its delta expression type.
type family Dual a = result | result -> a where
  Dual (OD.Array r) = DeltaD (Flip OR.Array) (Flip OS.Array) r
  Dual (AstDynamic r) = DeltaD AstRanked AstShaped r
  Dual (Flip OR.Array r n) = DeltaR (Flip OR.Array) r n
  Dual (AstRanked r n) = DeltaR AstRanked r n
  Dual (Flip OS.Array sh n) = DeltaS (Flip OR.Array) (Flip OS.Array) sh n
  Dual (AstShaped sh n) = DeltaS AstRanked AstShaped sh n


-- * Reverse pass, transpose/evaluation of the delta expressions

-- | The main input of the differentiation functions:
-- the delta expression to be differentiated and the dt perturbation
-- (small change) of the objective function codomain, for which we compute
-- the gradient.
data DeltaDt ranked shaped r =
    forall sh. OS.Shape sh
    => DeltaDtS () (DeltaS ranked shaped r sh)  -- TODO
  | forall n. KnownNat n
    => DeltaDtR (ranked r n) (DeltaR ranked r n)

-- | The state of evaluation. It consists of several maps.
-- The maps indexed by input identifiers and node identifiers
-- eventually store cotangents for their respective nodes.
-- The cotangents are built gradually during the evaluation,
-- by summing cotangent contributions.
--
-- Data invariant:
-- 1. keys dMap0 `intersect` keys dMapR == mempty
-- 2. keys nMap == keys dMap0 `union` keys dMapR
-- 3. key `member` dMap0 == nMap!key is DeltaBinding0
-- 4. key `member` dMapR == nMap!key is DeltaBindingR

-- TODO: remove 0, add S
data EvalState ranked shaped r = EvalState
  { iMap0       :: EM.EnumMap (InputId r) r
      -- ^ eventually, cotangents of objective function inputs of rank 0
      -- (finally copied to the vector representing the rank 0 portion
      -- of the gradient of the objective function);
      -- the identifiers need to be contiguous and start at 0
  , iMapR       :: EM.EnumMap (InputId (DynamicOf ranked r)) (DynamicOf ranked r)
      -- ^ eventually, cotangents of objective function inputs of rank R;
      -- (eventually copied to the vector representing the rank R portion
      -- of the gradient of the objective function);
      -- the identifiers need to be contiguous and start at 0
  , dMap0       :: EM.EnumMap NodeId r
      -- ^ eventually, cotangents of non-input subterms of rank 0 indexed
      -- by their node identifiers
  , dMapR       :: EM.EnumMap NodeId (DynamicOf ranked r)
      -- ^ eventually, cotangents of non-input subterms of rank R indexed
      -- by their node identifiers
  , nMap        :: EM.EnumMap NodeId (DeltaBinding ranked shaped r)
      -- ^ nodes left to be evaluated
  , astBindings :: [(AstVarId, DynamicOf ranked r)]
  }

-- | Nodes left to be evaluated.
-- We can't evaluate them at once, because their other shared copies
-- may still not be processed, so we'd not take advantage of the sharing
-- and not take into account the whole summed context when finally evaluating.
data DeltaBinding ranked shaped r =
    forall sh. OS.Shape sh
    => DeltaBindingS (DeltaS ranked shaped r sh)
  | forall n. KnownNat n
    => DeltaBindingR (DeltaR ranked r n)

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
-- value (usually set to @1@) is given in the @DeltaDt ranked r@ parameter.
gradientFromDelta
  :: forall ranked shaped r.
      (GoodScalar r, Tensor ranked, ConvertTensor ranked shaped)
  => Int -> DeltaDt ranked shaped r
  -> ([(AstVarId, DynamicOf ranked r)], Domains (DynamicOf ranked) r)
gradientFromDelta dimR deltaDt =
  -- Create finite maps that hold values associated with inputs
  -- and with (possibly shared) term tree nodes.
  -- The former are initialized with dummy values so that it's cheap
  -- to check if any update has already been performed to a cell
  -- (allocating big vectors filled with zeros is too costly,
  -- especially if never used in an iteration, and adding to such vectors
  -- and especially using them as cotangent accumulators is wasteful;
  -- additionally, it may not be easy to deduce the sizes of the vectors).
  let s0 =
        let iMap0 = EM.empty
            iMapR = EM.fromDistinctAscList
                    $ zip [toInputId 0 ..] (replicate dimR (ddummy @ranked))
            dMap0 = EM.empty
            dMapR = EM.empty
            nMap = EM.empty
            astBindings = []
        in EvalState {..}
  in let -- Eval.
         EvalState{..} = buildFinMaps s0 deltaDt
         -- Extract results.
         gradient = V.fromList $ EM.elems iMapR
     in (astBindings, gradient)
{-# SPECIALIZE gradientFromDelta
  :: Int -> DeltaDt (Flip OR.Array) (Flip OS.Array) Double
  -> ([(AstVarId, OD.Array Double)], DomainsOD Double) #-}
{-# SPECIALIZE gradientFromDelta
  :: Int -> DeltaDt AstRanked AstShaped Double
  -> ([(AstVarId, AstDynamic Double)], Domains AstDynamic Double) #-}

buildFinMaps
  :: forall ranked shaped r.
     (GoodScalar r, Tensor ranked, ConvertTensor ranked shaped)
  => EvalState ranked shaped r -> DeltaDt ranked shaped r
  -> EvalState ranked shaped r
buildFinMaps s0 deltaDt =
  -- The first argument is the evaluation state being modified,
  -- the second is the cotangent accumulator that will become an actual
  -- cotangent contribution when complete (see below for an explanation)
  -- and the third argument is the node to evaluate.
  let _evalS :: EvalState ranked shaped r -> r -> DeltaS ranked shaped r sh
             -> EvalState ranked shaped r
      _evalS _s !_c = \case
        LetS _n _d ->
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
          undefined

{-
        -- The general case is given as the last one below,
        -- but for a few constructors it's faster to inline @evalR@ instead.
        -- BTW, such an optimization doesn't really belong in the simplified
        -- horde-ad and no consistent benefit should be expected here.
        Index0 ZeroR _ _ -> s  -- shortcut
        Index0 (InputR (InputId i)) ixs' sh ->
          let ixs = indexToList ixs'
              f v = if isTensorDummy v
                    then treplicate0ND sh 0 `OD.update` [(ixs, c)]
                    else v `OD.update` [(ixs, v `tindex0D` ixs + c)]
          in s {iMapR = EM.adjust f (InputId i) $ iMapR s}
        Index0 (LetR n d) ixs' sh ->
          let ixs = indexToList ixs'
          in case EM.lookup n $ nMap s of
            Just (DeltaBindingR _) ->
              let f v = v `OD.update` [(ixs, v `tindex0D` ixs + c)]
              in s {dMapR = EM.adjust f n $ dMapR s}
                -- This would be an asymptotic optimization compared to
                -- the general case below, if not for the non-mutable update,
                -- which implies copying the whole @v@ vector,
                -- so it's only several times faster (same allocation,
                -- but not adding to each cell of @v@).
            Nothing ->
              let v = treplicate0ND sh 0 `OD.update` [(ixs, c)]
              in s { nMap = EM.insert n (DeltaBindingR d) $ nMap s
                   , dMapR = EM.insert n v $ dMapR s }
            _ -> error "buildFinMaps: corrupted nMap"
-}

      evalR :: forall n. KnownNat n
            => EvalState ranked shaped r
            -> ranked r n -> DeltaR ranked r n
            -> EvalState ranked shaped r
      evalR s !c = let (abShared, cShared) =
                         inline tregister c (astBindings s)
                       sShared = s {astBindings = abShared}
                   in \case
        ZeroR -> s
        InputR (InputId i) ->
          s {iMapR = EM.adjust (daddR c) (InputId i) $ iMapR s}
        ScaleR k d -> evalR s (k `tmult` c) d
        AddR d e -> evalR (evalR sShared cShared d) cShared e
        LetR n d ->
          assert (case d of
                    ZeroR -> False
                    DToR{} -> False
                    LetR{} -> False  -- wasteful and nonsensical
                    _ -> True)
          $ case EM.lookup n $ nMap s of
              Just (DeltaBindingR _) ->
                s {dMapR = EM.adjust (daddR c) n $ dMapR s}
              Nothing ->
                let cs = dfromR c
                in s { nMap = EM.insert n (DeltaBindingR d) $ nMap s
                     , dMapR = EM.insert n cs $ dMapR s }
              _ -> error "buildFinMaps: corrupted nMap"

        IndexR d ix sh -> evalR s (tscatter @ranked @r @0 sh c (const ix)) d
          -- equivalent: evalR s (updateNR (treplicate0NR sh 0) [(ix, c)]) d
        SumR n d -> evalR s (treplicate n c) d
        Sum0R sh d -> evalR s (treplicate0N sh c) d
        Dot0R v vd -> evalR s (v `tmult `treplicate0N (tshape v) c) vd
                     -- too slow: evalR s (tmap0N (* (tscalar c)) v) vd
        ScatterR _sh d f shd -> evalR s (tgather shd c f) d
        FromListR ld ->
          ifoldl' (\s2 i d2 ->
            evalR s2 (tindex cShared (fromIntegral i :. ZI)) d2) sShared ld
        FromVectorR ld ->
          V.ifoldl' (\s2 i d2 ->
            evalR s2 (tindex cShared (fromIntegral i :. ZI)) d2) sShared ld
        ReplicateR _n d -> evalR s (tsum c) d
        AppendR d k e -> case tshape c of
          n :$ _ -> let s2 = evalR sShared (tslice 0 k cShared) d
                    in evalR s2 (tslice k (n - k) cShared) e
          ZS -> error "evalR: appending a 0-dimensional tensor"
        SliceR i n d len -> case tshape c of
          n' :$ rest ->
            assert (n' == n `blame` (n', n)) $
            evalR s (tconcat [ tzero (i :$ rest)
                             , c
                             , tzero (len - i - n :$ rest) ])
                    d
          ZS -> error "evalR: slicing a 0-dimensional tensor"
        ReverseR d -> evalR s (treverse c) d
        TransposeR perm d ->
          let perm_reversed = map snd $ sort $ zip perm [0 .. length perm - 1]
          in evalR s (ttranspose perm_reversed c) d
        ReshapeR sh _sh' d -> evalR s (treshape sh c) d
        BuildR n f ->
          foldl' (\s2 i -> evalR s2 (tindex cShared (i :. ZI)) (f i))
                 sShared (fromIntegral <$> [0 .. n - 1])
        GatherR _sh d f shd -> evalR s (tscatter shd c f) d

        DToR @_ @_ @n2 (RToD @_ @_ @n1 d) ->
          case sameNat (Proxy @n1) (Proxy @n2) of
            Just Refl -> evalR s c d
            _ -> error "buildFinMaps: different ranks in DToR(RToD)"

      evalFromnMap :: EvalState ranked shaped r
                   -> EvalState ranked shaped r
      evalFromnMap s@EvalState{nMap, dMapR} =
        case EM.maxViewWithKey nMap of
          Just ((n, b), nMap2) ->
            let s2 = s {nMap = nMap2}
                s3 = case b of
                  DeltaBindingS _d -> undefined
                  DeltaBindingR d -> let c = tfromD $ dMapR EM.! n
                                     in evalR s2 c d
            in evalFromnMap s3
          Nothing -> s  -- loop ends

      s1 = case deltaDt of
        DeltaDtS _dt _deltaTopLevel -> undefined
        DeltaDtR dt deltaTopLevel -> evalR s0 dt deltaTopLevel
  in evalFromnMap s1
{-# SPECIALIZE buildFinMaps
  :: EvalState (Flip OR.Array) (Flip OS.Array) Double -> DeltaDt (Flip OR.Array) (Flip OS.Array) Double -> EvalState (Flip OR.Array) (Flip OS.Array) Double #-}
{-# SPECIALIZE buildFinMaps
  :: EvalState AstRanked AstShaped Double -> DeltaDt AstRanked AstShaped Double -> EvalState AstRanked AstShaped Double #-}


-- * Forward derivative computation from the delta expressions

-- Unlike @buildFinMaps@, the following is simpler written in ST
-- than with explicit passing of state, because changing the state here
-- is really an irritating side effect, while in @buildFinMaps@ it's building
-- the result. Perhaps this can be simplified completely differently.

-- This code is full of hacks (e.g., ST). Rewrites welcome.
-- Though perhaps let's wait for DeltaS.

-- | Forward derivative computation via forward-evaluation of delta-expressions
-- (which is surprisingly competitive to the direct forward method,
-- until the allocation of deltas gets large enough to affect cache hits).
-- This is the directional derivative, calculated for the point,
-- at which the delta expression was computed (which is the point
-- represented by the parameters of the objective function and used
-- to compute it's dual number result) and along the direction vector(s)
-- given in the last parameter called @ds@.
class ForwardDerivative (ranked :: Type -> Nat -> Type) a r where
  derivativeFromDelta
    :: Int -> Dual a -> Domains (DynamicOf ranked) r -> a

instance ( KnownNat n, GoodScalar r, Tensor ranked
         , ConvertTensor ranked shaped
         , Dual (ranked r n) ~ DeltaR ranked r n )
         => ForwardDerivative ranked (ranked r n) r where
  derivativeFromDelta dimR deltaTopLevel ds =
    case runST $ buildDerivative dimR (DeltaDtR 0 deltaTopLevel) ds of
      DeltaDtR @_ @_ @_ @n2 res _ -> case sameNat (Proxy @n) (Proxy @n2) of
        Just Refl -> res
        _ -> error "derivativeFromDelta"
      DeltaDtS{} -> error "derivativeFromDelta"

-- | This mimics 'buildFinMaps', but in reverse. Perhaps this can be
-- simplified, but the obvious simplest formulation does not honour sharing
-- and evaluates shared subexpressions repeatedly.
buildDerivative
  :: forall ranked shaped r s.
     (Tensor ranked, ConvertTensor ranked shaped, GoodScalar r)
  => Int -> DeltaDt ranked shaped r -> Domains (DynamicOf ranked) r
  -> ST s (DeltaDt ranked shaped r)
buildDerivative dimR deltaDt params = do
  dMapR <- newSTRef EM.empty
  nMap <- newSTRef EM.empty
  let evalR :: forall n. KnownNat n
            => DeltaR ranked r n -> ST s (ranked r n)
      evalR = \case
        ZeroR -> return $! tzero $ listShapeToShape $ replicate (valueOf @n) 1
          -- TODO: wrong shape but it often works and the special cases
          -- for ZeroR help, but the real solution would be shaped tensors
          -- or simplification of delta terms
        InputR (InputId i) ->
          if i < dimR
          then return $! tfromD $ params V.! i
          else error "derivativeFromDelta.eval': wrong index for an input"
        ScaleR _ ZeroR -> evalR ZeroR
        ScaleR k d -> tmult k <$> evalR d
        AddR ZeroR e -> evalR e
        AddR d ZeroR -> evalR d
        AddR d e -> liftM2 (\u v -> tsumOfList [u, v]) (evalR d) (evalR e)
        LetR n d -> do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBindingR _) -> do
              dm <- readSTRef dMapR
              return $! tfromD (dm EM.! n :: DynamicOf ranked r)
            Nothing -> do
              c <- evalR d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMapR
              writeSTRef nMap $! EM.insert n (DeltaBindingR d) nmNew
              writeSTRef dMapR $! EM.insert n (dfromR c) dm
              return c
            _ -> error "buildDerivative: corrupted nMap"

        IndexR d ix _len -> (`tindex` ix) <$> evalR d
        SumR _ d -> tsum <$> evalR d
        Sum0R _ ZeroR ->  return 0
        Sum0R _ d -> tsum0 <$> evalR d
        Dot0R _ ZeroR ->  return 0
        Dot0R v d -> tdot0 v <$> evalR d
        ScatterR sh d f _shd ->  do
          t <- evalR d
          return $! tscatter sh t f
        FromListR lsd -> do
          l <- mapM evalR lsd
          return $! tfromList l
        FromVectorR lsd -> do
          l <- V.mapM evalR lsd
          return $! tfromVector l
        ReplicateR n d -> do
          t <- evalR d
          return $! treplicate n t
        AppendR d _k e -> liftM2 tappend (evalR d) (evalR e)
        SliceR i n d _len -> tslice i n <$> evalR d
        ReverseR d -> treverse <$> evalR d
        TransposeR perm d -> ttranspose perm <$> evalR d
        ReshapeR _sh sh' d -> treshape sh' <$> evalR d
        BuildR n f -> do
          l <- mapM (evalR . f . fromIntegral) [0 .. n - 1]
          return $! tfromList l
        GatherR sh d f _shd -> do
          t <- evalR d
          return $! tgather sh t f

        DToR @_ @_ @n2 (RToD @_ @_ @n1 d) ->
          case sameNat (Proxy @n1) (Proxy @n2) of
            Just Refl -> evalR d
            _ -> error "buildDerivative: different ranks in DToR(RToD)"

  -- A hack to fit both argument delta and, afterwards, the result in a type
  -- that does not reflect either.
  case deltaDt of
    DeltaDtS _dt _deltaTopLevel -> undefined  -- TODO
    DeltaDtR _dt deltaTopLevel ->
      flip DeltaDtR ZeroR <$> evalR deltaTopLevel
