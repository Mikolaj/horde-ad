{-# LANGUAGE AllowAmbiguousTypes, DerivingStrategies, UndecidableInstances #-}
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
module HordeAd.Core.Delta
  ( -- * Delta expression evaluation
    gradientFromDelta, derivativeFromDelta, interpretationConstant
    -- * Abstract syntax trees of the delta expressions
  , DeltaR (..), DeltaS (..), Delta(..)
  , -- * Delta expression identifiers
    NodeId (..), InputId, toInputIdR, toInputIdS
    -- * Exported to be specialized elsewhere
  , evalFromnMap, EvalState
  ) where

import Prelude

import Control.Arrow (second)
import Control.Exception.Assert.Sugar
import Data.Array.Shape qualified as Sh
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.Int (Int64)
import Data.Kind (Type)
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Some
import Data.Strict.Vector qualified as Data.Vector
import Data.Traversable (mapAccumL)
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Foreign.C (CInt)
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, sameNat, type (+), type (<=))
import Text.Show.Functions ()
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape qualified as X
import Data.Array.Mixed.Types qualified as X
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.ShapedList (IndexSh, pattern (:.$), pattern ZIS)
import HordeAd.Util.SizedList

-- * Reverse and forward derivative computation for HVectorPseudoTensor

gradientFromDelta
  :: forall ranked y. (ADReady ranked, TensorKind y)
  => VoidHVector
  -> InterpretationTarget ranked y
  -> Maybe (InterpretationTarget ranked y)
  -> Delta ranked y
  -> HVector ranked
gradientFromDelta !parameters0 value !mdt deltaTopLevel =
  let oneAtF = interpretationConstant 1 $ tshapeFull (stensorKind @y) value
      dt = fromMaybe oneAtF mdt
      s0 = initEvalState parameters0
      s1 = evalR s0 dt deltaTopLevel
      s2 = evalFromnMap s1
      toDynamicTensor :: Some (InterpretationTargetM ranked)
                      -> DynamicTensor ranked
      toDynamicTensor (Some b) = case b of
        MTKR @r @n t -> DynamicRanked @r @n t
        MTKS @r @sh t -> DynamicShaped @r @sh t
        MTKRDummy @r @sh -> DynamicRankedDummy @r @sh Proxy Proxy
        MTKSDummy @r @sh -> DynamicShapedDummy @r @sh Proxy Proxy
        MTKProduct{} -> error "toDynamicTensor: currently impossible"
        MTKUntyped{} -> error "toDynamicTensor: currently impossible"
  in V.fromList $ map toDynamicTensor $ DMap.elems $ iMap s2

interpretationConstant :: forall ranked y. ADReady ranked
                       => (forall r. GoodScalar r => r)
                       -> TensorKindFull y -> InterpretationTarget ranked y
interpretationConstant r = \case
  FTKR sh -> rrepl (toList sh) r
  FTKS -> srepl r
  FTKProduct ftk1 ftk2 -> ( interpretationConstant r ftk1
                          , interpretationConstant r ftk2 )
  FTKUntyped ssh ->  -- TODO: if r is 0, this would be cheaper with Dummy
    HVectorPseudoTensor $ dmkHVector
    $ mapHVectorShaped (const $ srepl @_ @_ @(ShapedOf ranked) r)
    $ V.map dynamicFromVoid ssh

derivativeFromDelta
  :: forall ranked y. ADReady ranked
  => Int -> Delta ranked y -> HVector ranked
  -> InterpretationTarget ranked y
derivativeFromDelta dim deltaTopLevel ds =
  -- EvalState is too complex for the forward derivative, but since
  -- it's already defined, let's use it.
  let s0 = EvalState DMap.empty DMap.empty DMap.empty
      !(!_s2, !c) = fwdR dim ds s0 deltaTopLevel
  in c


-- * Abstract syntax trees of the delta expressions

-- | TODO: This and most of other haddocks are out of date.
--
-- For each choice of the underlying scalar type @r@,
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
-- The `NodeId` identifier that appears in a @ShareR n d@ expression
-- is the unique identity stamp of subterm @d@, that is, there is
-- no different term @e@ such that @ShareR n e@ appears in any delta
-- expression term in memory during the same run of an executable.
-- The subterm identity is used to avoid evaluating shared
-- subterms repeatedly in gradient and derivative computations.
-- The identifier also represents data dependencies among terms
-- for the purpose of gradient and derivative computation. Computation for
-- a term may depend only on data obtained from terms with lower value
-- of their node identifiers. Such data dependency determination
-- agrees with the subterm relation, but is faster than traversing
-- the term tree in order to determine the relation of terms.
--
-- There is one exception to the subterm data dependency rule:
-- any term containing a function (e.g., a @Gather@ node)
-- may depend on terms generated by applying the function,
-- regardless of their node identifiers (which in our implementation
-- are going to be larger than their ancestors').
-- Note that the functions inside constructors can be readily converted
-- to AST terms (with distinguished variables) when we are working
-- in an AST instance. However, this is not needed, because the AST term
-- resulting from differentiation for that instance won't have any functions
-- embedded, so there's no problem with sending Haskell closures to a GPU.
-- And in other instances we can't directly use GPUs anyway (though we can
-- indirectly, e.g., via ArrayFire), because we don't produce AST terms
-- that could be compiled for a GPU, so we don't worry about it.
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
--
-- This is the grammar of delta-expressions corresponding to ranked tensors.
-- The comments refer to the ordinary (forward) semantics of the terms,
-- as given in @buildDerivative@. Evaluating the terms backwards
-- (transposing the represented linear map) in order to compute gradients
-- provides a different semantics.

-- The old DeltaR reconstructed:
type role DeltaR nominal nominal nominal
newtype DeltaR ranked r n =
  DeltaR {unDeltaR :: Delta ranked (TKR r n)}
instance ( RankedOf (ShapedOf ranked) ~ ranked
         , GoodScalar r, Show (IntOf ranked)
         , Show (IntOf (ShapedOf ranked))
         , CRanked ranked Show
         , CShaped (ShapedOf ranked) Show )
         => Show (DeltaR ranked r n) where
  showsPrec k (DeltaR t) = showsPrec k t
    -- to keep PP tests passing regardless of what wrappers we currently use

-- The old DeltaS reconstructed:
type role DeltaS nominal nominal nominal
type DeltaS :: ShapedTensorType -> ShapedTensorType
newtype DeltaS shaped r sh =
  DeltaS {unDeltaS :: Delta (RankedOf shaped) (TKS r sh)}
instance ( ranked ~ RankedOf shaped, RankedOf (ShapedOf ranked) ~ ranked
         , GoodScalar r, Show (IntOf ranked)
         , Show (IntOf (ShapedOf ranked))
         , CRanked ranked Show
         , CShaped (ShapedOf ranked) Show )
         => Show (DeltaS shaped r sh) where
  showsPrec k (DeltaS t) = showsPrec k t
    -- to keep PP tests passing regardless of what wrappers we currently use

type role Delta nominal nominal
data Delta :: RankedTensorType -> TensorKindType -> Type where
  TupleG :: (TensorKind y, TensorKind z)
         => Delta ranked y -> Delta ranked z
         -> Delta ranked (TKProduct y z)
  Project1G :: forall x z ranked. TensorKind z
            => Delta ranked (TKProduct x z) -> Delta ranked x
  Project2G :: forall x z ranked. TensorKind x
            => Delta ranked (TKProduct x z) -> Delta ranked z

  ZeroR :: (KnownNat n, GoodScalar r) => IShR n -> Delta ranked (TKR r n)
    -- ^ the shape is required for @shapeDelta@ and forward derivative
  InputR :: forall ranked r n. (GoodScalar r, KnownNat n)
         => IShR n -> InputId ranked (TKR r n) -> Delta ranked (TKR r n)
  ScaleR :: (KnownNat n, GoodScalar r)
         =>  ranked r n -> Delta ranked (TKR r n) -> Delta ranked (TKR r n)
  AddR :: (GoodScalar r, KnownNat n)
       => Delta ranked (TKR r n) -> Delta ranked (TKR r n)
       -> Delta ranked (TKR r n)
  ShareR :: (GoodScalar r, KnownNat n)
         => NodeId ranked (TKR r n) -> Delta ranked (TKR r n) -> Delta ranked (TKR r n)

  IndexR :: (GoodScalar r, KnownNat n, KnownNat m)
         => Delta ranked (TKR r (m + n)) -> IndexOf ranked m
         -> Delta ranked (TKR r n)
    -- ^ The sub-tensor at the given index. The given shape is of the
    -- large tensor. If index is out of bounds, the result is defined and is 0.
  SumR :: (GoodScalar r, KnownNat n)
       => Delta ranked (TKR r (1 + n)) -> Delta ranked (TKR r n)
  Sum0R :: (GoodScalar r, KnownNat n)
        => Delta ranked (TKR r n) -> Delta ranked (TKR r 0)
  Dot0R :: (KnownNat n, GoodScalar r)
        => ranked r n -> Delta ranked (TKR r n) -> Delta ranked (TKR r 0)
  ScatterR :: (GoodScalar r, KnownNat m, KnownNat p, KnownNat n)
           => IShR (p + n) -> Delta ranked (TKR r (m + n))
           -> (IndexOf ranked m -> IndexOf ranked p)
           -> Delta ranked (TKR r (p + n))
    -- ^ Build a tensor by adding up tensors of rank @n@ taken from
    -- the third argument and inserted in a zero tensor
    -- at indexes of length @p@. Indexes of length 0 insert tensors trivially,
    -- so that, e.g, @Scatter1 5 (const ZR) (Replicate0R [5] d) []@ is equivalent
    -- to @5 * d@. If an index of length @p@ is out of bounds, no tensor
    -- is added at such an index (and similarly in @ScatterN@).
    -- The semantics of the operation permits index out of bounds
    -- and then no tensors is added at such an index.
    -- TODO: this is a haddock for Scatter1; fix.

  FromVectorR :: (KnownNat n, GoodScalar r)
              => Data.Vector.Vector (Delta ranked (TKR r n))
              -> Delta ranked (TKR r (1 + n))
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  ReplicateR :: (GoodScalar r, KnownNat n)
             => Int -> Delta ranked (TKR r n)
             -> Delta ranked (TKR r (1 + n))
    -- ^ Copy the given tensor along the new, outermost dimension.
  AppendR :: (GoodScalar r, KnownNat n)
          => Delta ranked (TKR r (1 + n))
          -> Delta ranked (TKR r (1 + n))
          -> Delta ranked (TKR r (1 + n))
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
  SliceR :: (GoodScalar r, KnownNat n)
         => Int -> Int -> Delta ranked (TKR r (1 + n))
         -> Delta ranked (TKR r (1 + n))
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
  ReverseR :: (GoodScalar r, KnownNat n)
           => Delta ranked (TKR r (1 + n)) -> Delta ranked (TKR r (1 + n))
    -- ^ Reverse elements of the outermost dimension.
  TransposeR :: (GoodScalar r, KnownNat n)
             => Permutation.PermR -> Delta ranked (TKR r n)
             -> Delta ranked (TKR r n)
    -- ^ Transpose according to the permutation.
  ReshapeR :: (GoodScalar r, KnownNat n, KnownNat m)
           => IShR m -> Delta ranked (TKR r n)
           -> Delta ranked (TKR r m)
    -- ^ Change the shape of the tensor to the given one.
  GatherR :: (GoodScalar r, KnownNat m, KnownNat p, KnownNat n)
          => IShR (m + n) -> Delta ranked (TKR r (p + n))
          -> (IndexOf ranked m -> IndexOf ranked p)
          -> Delta ranked (TKR r (m + n))
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @Gather1 (const ZR) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @GatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for Gather1; fix.
  CastR :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2, KnownNat n)
        => Delta ranked (TKR r1 n) -> Delta ranked (TKR r2 n)
  RFromS :: forall sh r ranked. (GoodScalar r, KnownShS sh)
         => Delta ranked (TKS r sh)
         -> Delta ranked (TKR r (X.Rank sh))
  RFromH :: (GoodScalar r, KnownNat n)
         => Delta ranked TKUntyped -> Int -> Delta ranked (TKR r n)

  ZeroS :: (GoodScalar r, KnownShS sh) => Delta ranked (TKS r sh)
  InputS :: forall ranked r sh. (GoodScalar r, KnownShS sh)
         => InputId ranked (TKS r sh) -> Delta ranked (TKS r sh)
  ScaleS :: (KnownShS sh, GoodScalar r)
         => ShapedOf ranked r sh -> Delta ranked (TKS r sh)
         -> Delta ranked (TKS r sh)
  AddS :: (GoodScalar r, KnownShS sh)
       => Delta ranked (TKS r sh) -> Delta ranked (TKS r sh)
       -> Delta ranked (TKS r sh)
  ShareS :: (GoodScalar r, KnownShS sh)
         => NodeId ranked (TKS r sh) -> Delta ranked (TKS r sh) -> Delta ranked (TKS r sh)

  IndexS :: (KnownShS sh1, KnownShS sh2, KnownShS (sh1 X.++ sh2), GoodScalar r)
         => Delta ranked (TKS r (sh1 X.++ sh2))
         -> IndexSh (ShapedOf ranked) sh1
         -> Delta ranked (TKS r sh2)
    -- ^ The sub-tensor at the given index.
    -- If index is out of bounds, the result is defined and is 0.
  SumS :: (GoodScalar r, KnownNat n, KnownShS sh)
       => Delta ranked (TKS r (n ': sh)) -> Delta ranked (TKS r sh)
  Sum0S :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Internal.Shape.Product sh))
        => Delta ranked (TKS r sh) -> Delta ranked (TKS r '[])
  Dot0S :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Internal.Shape.Product sh))
        => ShapedOf ranked r sh -> Delta ranked (TKS r sh)
        -> Delta ranked (TKS r '[])
  ScatterS :: forall ranked r sh2 p sh.
              ( GoodScalar r, KnownShS sh2, KnownShS sh, KnownNat p
              , KnownShS (Sh.Take p sh), KnownShS (Sh.Drop p sh)
              , KnownShS (sh2 X.++ Sh.Drop p sh) )
           => Delta ranked (TKS r (sh2 X.++ Sh.Drop p sh))
           -> (IndexSh (ShapedOf ranked) sh2
               -> IndexSh (ShapedOf ranked) (Sh.Take p sh))
           -> Delta ranked (TKS r sh)
    -- ^ Build a tensor by adding up tensors of rank @n@ taken from
    -- the third argument and inserted in a zero tensor
    -- at indexes of length @p@. Indexes of length 0 insert tensors trivially,
    -- so that, e.g, @Scatter1 5 (const ZR) (Replicate0R [5] d) []@ is equivalent
    -- to @5 * d@. If an index of length @p@ is out of bounds, no tensor
    -- is added at such an index (and similarly in @ScatterN@).
    -- The semantics of the operation permits index out of bounds
    -- and then no tensors is added at such an index.
    -- TODO: this is a haddock for Scatter1; fix.

  FromVectorS :: (GoodScalar r, KnownShS sh, KnownNat n)
              => Data.Vector.Vector (Delta ranked (TKS r sh))
              -> Delta ranked (TKS r (n ': sh))
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  ReplicateS :: forall ranked r n sh.
                (GoodScalar r, KnownShS sh, KnownNat n)
             => Delta ranked (TKS r sh) -> Delta ranked (TKS r (n ': sh))
    -- ^ Copy the given tensor along the new, outermost dimension.
  AppendS :: forall ranked r m n sh.
             (GoodScalar r, KnownNat m, KnownNat n, KnownShS sh)
          => Delta ranked (TKS r (m ': sh))
          -> Delta ranked (TKS r (n ': sh))
          -> Delta ranked (TKS r ((m + n) ': sh))
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
    -- The integer argument is the outermost size of the first array.
  SliceS :: forall ranked i n k r sh.
            (GoodScalar r, KnownNat i, KnownNat n, KnownNat k, KnownShS sh)
         => Delta ranked (TKS r (i + n + k ': sh))
         -> Delta ranked (TKS r (n ': sh))
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
    -- The last argument is the outermost size of the argument array.
  ReverseS :: (GoodScalar r, KnownShS sh, KnownNat n)
           => Delta ranked (TKS r (n ': sh))
           -> Delta ranked (TKS r (n ': sh))
    -- ^ Reverse elements of the outermost dimension.
  TransposeS :: forall perm sh r ranked.
                (GoodScalar r, PermC perm, KnownShS sh, X.Rank perm <= X.Rank sh)
             => Permutation.Perm perm
             -> Delta ranked (TKS r sh)
             -> Delta ranked (TKS r (Permutation.PermutePrefix perm sh))
    -- ^ Transpose according to the permutation.
  ReshapeS :: ( GoodScalar r, KnownShS sh, KnownShS sh2
              , Nested.Internal.Shape.Product sh
                ~ Nested.Internal.Shape.Product sh2 )
           => Delta ranked (TKS r sh)
           -> Delta ranked (TKS r sh2)
    -- ^ Change the shape of the tensor from the first to the second.
  GatherS :: forall ranked r sh2 p sh.
             ( GoodScalar r, KnownShS sh2, KnownShS sh, KnownNat p
             , KnownShS (Sh.Take p sh), KnownShS (Sh.Drop p sh)
             , KnownShS (sh2 X.++ Sh.Drop p sh) )
          => Delta ranked (TKS r sh)
          -> (IndexSh (ShapedOf ranked) sh2
              -> IndexSh (ShapedOf ranked) (Sh.Take p sh))
          -> Delta ranked (TKS r (sh2 X.++ Sh.Drop p sh))
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @Gather1 (const ZR) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @GatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for Gather1; fix.
  CastS :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2, KnownShS sh)
        => Delta ranked (TKS r1 sh) -> Delta ranked (TKS r2 sh)
  SFromR :: forall sh r ranked. (GoodScalar r, KnownShS sh, KnownNat (X.Rank sh))
         => Delta ranked (TKR r (X.Rank sh))
         -> Delta ranked (TKS r sh)
  SFromH :: (GoodScalar r, KnownShS sh)
         => Delta ranked TKUntyped -> Int -> Delta ranked (TKS r sh)

  ShareH :: NodeId ranked TKUntyped -> Delta ranked TKUntyped
         -> Delta ranked TKUntyped
  HToH :: HVector (DeltaR ranked) -> Delta ranked TKUntyped
  MapAccumR
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> HVector ranked
    -> HVector ranked
    -> HFun (TKProduct TKUntyped TKUntyped) TKUntyped
    -> HFun (TKProduct TKUntyped TKUntyped) TKUntyped
    -> HVector (DeltaR ranked)
    -> HVector (DeltaR ranked)
    -> Delta ranked TKUntyped
  MapAccumL
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> HVector ranked
    -> HVector ranked
    -> HFun (TKProduct TKUntyped TKUntyped) TKUntyped
    -> HFun (TKProduct TKUntyped TKUntyped) TKUntyped
    -> HVector (DeltaR ranked)
    -> HVector (DeltaR ranked)
    -> Delta ranked TKUntyped

deriving instance ( RankedOf (ShapedOf ranked) ~ ranked
                  , Show (IntOf ranked)
                  , Show (IntOf (ShapedOf ranked))
                  , CRanked ranked Show
                  , CShaped (ShapedOf ranked) Show )
                  => Show (Delta ranked y)

-- This is needed for the Show instances due to HVector (Delta...)
-- referring to ShapedOf (Delta..).
type instance RankedOf (DeltaS shaped) = DeltaR (RankedOf shaped)

type instance ShapedOf (DeltaR ranked) = DeltaS (ShapedOf ranked)

type instance HVectorOf (DeltaR ranked) = Delta ranked TKUntyped

instance ProductTensor (DeltaR ranked) where
  tmkHVector = HToH

shapeDeltaFull :: forall ranked y.
                  (TensorKind y, RankedOf (ShapedOf ranked) ~ ranked)
               => Delta ranked y -> TensorKindFull y
shapeDeltaFull = \case
  TupleG t1 t2 -> FTKProduct (shapeDeltaFull t1) (shapeDeltaFull t2)
  Project1G v -> case shapeDeltaFull v of
    FTKProduct ftk1 _ -> ftk1
  Project2G v -> case shapeDeltaFull v of
    FTKProduct _ ftk2 -> ftk2

  ZeroR sh -> FTKR sh
  InputR sh _ -> FTKR sh
  ScaleR _ d -> shapeDeltaFull d
  AddR d _ -> shapeDeltaFull d
  ShareR _ d -> shapeDeltaFull d
  IndexR d _ -> FTKR $ dropShape (shapeDelta d)
  SumR d -> FTKR $ tailShape (shapeDelta d)
  Sum0R{} -> FTKR $ ZSR
  Dot0R{} -> FTKR $ ZSR
  ScatterR sh _ _ -> FTKR sh
  FromVectorR l -> case V.toList l of
    [] -> case stensorKind @y of
      STKR @_ @n _ _ -> case sameNat (Proxy @n) (Proxy @1) of
        Just Refl -> FTKR $ singletonShape 0  -- the only case where we can guess sh
        _ -> error "shapeDeltaFull: FromVectorR with no arguments"
    d : _ -> FTKR $ length l :$: shapeDelta d
  ReplicateR n d -> FTKR $ n :$: shapeDelta d
  AppendR x y -> case shapeDelta x of
    ZSR -> error "shapeDeltaFull: impossible pattern needlessly required"
    xi :$: xsh -> case shapeDelta y of
      ZSR -> error "shapeDeltaFull: impossible pattern needlessly required"
      yi :$: _ -> FTKR $ xi + yi :$: xsh
  SliceR _ n d -> FTKR $ n :$: tailShape (shapeDelta d)
  ReverseR d -> shapeDeltaFull d
  TransposeR perm d -> FTKR $ Nested.Internal.Shape.shrPermutePrefix perm (shapeDelta d)
  ReshapeR sh _ -> FTKR sh
  GatherR sh _ _ -> FTKR sh
  CastR d -> FTKR $ shapeDelta d
  RFromS @sh _ | Dict <- lemKnownNatRank (knownShS @sh) ->
    FTKR $ listToShape $ shapeT @sh
  RFromH d i -> FTKR $ listToShape $ shapeVoidDynamic (shapeDeltaH d V.! i)

  ZeroS{} -> FTKS
  InputS{} -> FTKS
  ScaleS{} -> FTKS
  AddS{} -> FTKS
  ShareS{} -> FTKS
  IndexS{} -> FTKS
  SumS{} -> FTKS
  Sum0S{} -> FTKS
  Dot0S{} -> FTKS
  ScatterS{} -> FTKS
  FromVectorS{} -> FTKS
  ReplicateS{} -> FTKS
  AppendS{} -> FTKS
  SliceS{} -> FTKS
  ReverseS{} -> FTKS
  TransposeS @perm @sh2 perm _v ->
    withShapeP
      (permutePrefixList (Permutation.permToList' perm)
                         (shapeT @sh2)) $ \(Proxy @sh2Perm) ->
        gcastWith (unsafeCoerce Refl :: sh2Perm :~: Permutation.PermutePrefix perm sh2)
        FTKS
  ReshapeS{} -> FTKS
  GatherS{} -> FTKS
  CastS{} -> FTKS
  SFromR{} -> FTKS
  SFromH{} -> FTKS

  ShareH _ d -> shapeDeltaFull d
  HToH v ->
    FTKUntyped $ V.map (voidFromDynamicF (shapeToList . shapeDelta . unDeltaR)) v
  MapAccumR k accShs bShs _eShs _q _es _df _rf _acc0' _es' ->
    FTKUntyped $ accShs V.++ replicate1VoidHVector k bShs
  MapAccumL k accShs bShs _eShs _q _es _df _rf _acc0' _es' ->
    FTKUntyped $ accShs V.++ replicate1VoidHVector k bShs

shapeDelta :: forall ranked r n.
              (GoodScalar r, KnownNat n, RankedOf (ShapedOf ranked) ~ ranked)
           => Delta ranked (TKR r n) -> IShR n
shapeDelta t = case shapeDeltaFull t of
  FTKR sh -> sh

lengthDelta :: forall ranked r n.
               (GoodScalar r, KnownNat n, RankedOf (ShapedOf ranked) ~ ranked)
            => Delta ranked (TKR r (1 + n)) -> Int
lengthDelta d = case shapeDelta d of
  ZSR -> error "lengthDelta: impossible pattern needlessly required"
  k :$: _ -> k

shapeDeltaH :: forall ranked. RankedOf (ShapedOf ranked) ~ ranked
            => Delta ranked TKUntyped -> VoidHVector
shapeDeltaH t = case shapeDeltaFull t of
  FTKUntyped shs -> shs


-- * Delta expression identifiers and evaluation state

type role NodeId nominal nominal
data NodeId :: RankedTensorType -> TensorKindType -> Type where
  NodeId :: forall ranked y. TensorKind y => Int -> NodeId ranked y

instance Show (NodeId ranked y) where
  showsPrec d (NodeId n) =
    showsPrec d n  -- less verbose, more readable

  -- No Eq instance to limit hacks outside this module.
instance TensorKind y => Enum (NodeId ranked y) where
  toEnum = NodeId
  fromEnum (NodeId n) = n

instance DMap.Enum1 (NodeId ranked) where
  type Enum1Info (NodeId ranked) = Some (Dict TensorKind)
  fromEnum1 (NodeId @_ @a n) = (n, Some @_ @a Dict)
  toEnum1 n (Some @_ @a Dict) = Some $ NodeId @ranked @a n

type role InputId nominal nominal
data InputId :: RankedTensorType -> TensorKindType -> Type where
  InputId :: forall ranked y. TensorKind y => Int -> InputId ranked y

deriving instance Show (InputId ranked y)
instance TensorKind y => Enum (InputId ranked y) where
  toEnum = InputId
  fromEnum (InputId n) = n

instance DMap.Enum1 (InputId ranked) where
  type Enum1Info (InputId ranked) = Some (Dict TensorKind)
  fromEnum1 (InputId @_ @a n) = (n, Some @_ @a Dict)
  toEnum1 n (Some @_ @a Dict) = Some $ InputId @ranked @a n

-- | Wrap non-negative (only!) integers in the `InputId` newtype.
toInputIdR :: (GoodScalar r, KnownNat n) => Int -> InputId f (TKR r n)
toInputIdR i = assert (i >= 0) $ InputId i

toInputIdS :: (GoodScalar r, KnownShS sh) => Int -> InputId f (TKS r sh)
toInputIdS i = assert (i >= 0) $ InputId i

-- | The state of evaluation. It consists of several maps.
-- The maps indexed by input identifiers and node identifiers
-- eventually store cotangents for their respective nodes.
-- The cotangents are built gradually during the evaluation,
-- by summing cotangent contributions.
--
-- Data invariant:
-- 1. keys nMap == keys dMap
-- 2. key `member` dMap == nMap!key is DynamicRanked
type role EvalState nominal
data EvalState ranked = EvalState
  { iMap :: DEnumMap (InputId ranked) (InterpretationTargetM ranked)
      -- ^ eventually, cotangents of objective function inputs
      -- (eventually copied to the vector representing the gradient
      -- of the objective function);
      -- the identifiers need to be contiguous and start at 0
  , dMap :: DEnumMap (NodeId ranked) (InterpretationTargetD ranked)
      -- ^ eventually, cotangents of non-input subterms indexed
      -- by their node identifiers
  , nMap :: DEnumMap (NodeId ranked) (Delta ranked)
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
  :: VoidHVector -> EvalState ranked
initEvalState !parameters0 =
  -- Create finite maps that hold values associated with inputs
  -- and with (possibly shared) term tree nodes.
  -- The former are usually initialized with dummy values so that it's cheap
  -- to check if any update has already been performed to a cell
  -- (allocating big vectors filled with zeros is too costly,
  -- especially if never used in an iteration, and adding to such vectors
  -- and especially using them as cotangent accumulators is wasteful.
  -- We take care to keep the scalar type of the dummy correct,
  -- but a shape is not preserved in a dummy, so it's not shape-correct.
  let fromDynamicTensor
        :: forall ranked.
           Int -> DynamicTensor ranked
        -> DSum (InputId ranked) (InterpretationTargetM ranked)
      fromDynamicTensor n b = case b of
        DynamicRanked t -> InputId n :=> MTKR t
        DynamicShaped t -> InputId n :=> MTKS t
        DynamicRankedDummy @r @sh _ _ | Dict <- lemKnownNatRank (knownShS @sh) ->
          InputId n :=> MTKRDummy @r @sh
        DynamicShapedDummy @r @sh _ _ ->
          InputId n :=> MTKSDummy @r @sh
      iMap = DMap.fromDistinctAscList $ zipWith fromDynamicTensor [0 ..]
             $ map dynamicFromVoid $ V.toList parameters0
      dMap = DMap.empty
      nMap = DMap.empty
  in EvalState {..}


-- * Reverse pass, transpose/evaluation of the delta expressions

-- The first argument is the evaluation state being modified,
-- the second is the cotangent accumulator that will become an actual
-- cotangent contribution when complete (see below for an explanation)
-- and the third argument is the node to evaluate.
evalRRuntimeSpecialized
  :: forall n r ranked. (GoodScalar r, KnownNat n, ADReady ranked)
  => EvalState ranked
  -> ranked r n -> Delta ranked (TKR r n)
  -> EvalState ranked
evalRRuntimeSpecialized !s !c =
  -- We dispatch on all expected underyling scalar types, which is
  -- necessary to run the correct specialization when unpacking
  -- an existential type. All IfDifferentiable and RowSum instances should
  -- be included in the list of expected underlying scalar types.
  -- If the scalar type is not on the list, performance suffers greatly.
  -- TODO: can I pattern match on (typeRep @r) instead?
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalR @(TKR Double n) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalR @(TKR Float n) s c
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> evalR @(TKR Int64 n) s c
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> evalR @(TKR CInt n) s c
          _ -> error "evalRRuntimeSpecialized: unexpected scalar"

evalSRuntimeSpecialized
  :: forall sh r ranked. (GoodScalar r, KnownShS sh, ADReady ranked)
  => EvalState ranked -> ShapedOf ranked r sh -> Delta ranked (TKS r sh)
  -> EvalState ranked
evalSRuntimeSpecialized !s !c =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalR @(TKS Double sh) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalR @(TKS Float sh) s c
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> evalR @(TKS Int64 sh) s c
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> evalR @(TKS CInt sh) s c
          _ -> error "evalSRuntimeSpecialized: unexpected scalar"

addInterpretationTargetD ::
  ADReady ranked
  => InterpretationTargetD ranked y
  -> InterpretationTargetD ranked y
  -> InterpretationTargetD ranked y
addInterpretationTargetD a b = case (a, b) of
  (DTKR ta, DTKR tb) -> DTKR $ ta + tb
  (DTKS ta, DTKS tb) -> DTKS $ ta + tb
  (DTKProduct ta1 ta2, DTKProduct tb1 tb2) ->
    DTKProduct (addInterpretationTargetD ta1 tb1)
               (addInterpretationTargetD ta2 tb2)
  (DTKUntyped hv1, DTKUntyped hv2) ->
    DTKUntyped $ dmkHVector
    $ V.zipWith addDynamic (dunHVector hv1) (dunHVector hv2)
      -- dunHVector is fine, because anything inside DTKUntyped either
      -- already a packed HVector or is shared (e.g., a shared variable)

addInterpretationTargetM ::
  ADReady ranked
  => InterpretationTargetM ranked y
  -> InterpretationTargetM ranked y
  -> InterpretationTargetM ranked y
addInterpretationTargetM a b = case (a, b) of
  (MTKR ta, MTKR tb) -> MTKR $ ta + tb
  (MTKRDummy, _) -> b
  (_, MTKRDummy) -> a
  (MTKS ta, MTKS tb) -> MTKS $ ta + tb
  (MTKSDummy, _) -> b
  (_, MTKSDummy) -> a
  (MTKProduct ta1 ta2, MTKProduct tb1 tb2) ->
    MTKProduct (addInterpretationTargetM ta1 tb1)
               (addInterpretationTargetM ta2 tb2)
  (MTKUntyped hv1, MTKUntyped hv2) ->
    MTKUntyped $ dmkHVector
    $ V.zipWith addDynamic (dunHVector hv1) (dunHVector hv2)

evalR
  :: forall y ranked. (TensorKind y, ADReady ranked)
  => EvalState ranked -> InterpretationTarget ranked y -> Delta ranked y
  -> EvalState ranked
evalR !s !c = \case
  TupleG d1 d2 -> -- TODO: let cShared = rshare c
                  evalR (evalR s (fst c) d1) (snd c) d2
  Project1G d -> case shapeDeltaFull d of
    FTKProduct _ ftk2 ->
      let zero = interpretationConstant 1 ftk2
      in evalR s (c, zero) d
  Project2G d -> case shapeDeltaFull d of
    FTKProduct ftk1 _ ->
      let zero = interpretationConstant 1 ftk1
      in evalR s (zero, c) d

  ZeroR{} -> s
  InputR _ i -> let cs = MTKR c
                in s {iMap = DMap.adjust (addInterpretationTargetM cs) i
                             $ iMap s}
    -- This and similar don't need to be runtime-specialized,
    -- because the type of c determines the Num instance for (+).
    -- Note that we can't express sharing by inserting Share constructors
    -- into iMap, because often sharing needs to work across many
    -- iMap keys. That's why global sharing is used.
  ScaleR k d -> evalR s (k * c) d
  AddR d e -> let cShared = rshare c
              in evalR (evalR s cShared d) cShared e
  ShareR n d ->
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
    -- corresponding to the shared term @ShareR n d@. This total
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
    assert (case d of
              ZeroR{} -> False
              ShareR{} -> False  -- wasteful and nonsensical
              _ -> True)
    $ let cs = DTKR c
      in case DMap.lookup n $ nMap s of
        Just _ ->
          s {dMap = DMap.adjust (addInterpretationTargetD cs) n $ dMap s}
        Nothing ->
          s { nMap = DMap.insert n d $ nMap s
            , dMap = DMap.insert n cs $ dMap s }

  IndexR d ix -> evalR s (rscatter @ranked @_ @0
                                   (shapeDelta d) c (const ix)) d
    -- equivalent: evalR s (updateNR (treplicate0NR sh 0) [(ix, c)]) d
  SumR d -> evalR s (rreplicate (lengthDelta d) c) d
  Sum0R d -> evalR s (rreplicate0N (shapeDelta d) c) d
  Dot0R v vd -> evalR s (v * rreplicate0N (rshape v) c) vd
                  -- too slow: evalR s (rmap0N (* (tscalar c)) v) vd
  ScatterR _sh d f -> evalR s (rgather (shapeDelta d) c f) d

  FromVectorR @n1 @r ld ->
    let cShared = rshare c
        cxs :: [ranked r n1]
        cxs = runravelToList cShared
    in foldl' (\ !s2 (cx, d2) -> evalR s2 cx d2) s
       $ zip cxs (V.toList ld)
  ReplicateR _n d -> evalR s (rsum c) d
  AppendR d e -> case rshape c of
    n :$: _ -> let cShared = rshare c
                   k = lengthDelta d
                   s2 = evalR s (rslice 0 k cShared) d
               in evalR s2 (rslice k (n - k) cShared) e
    ZSR -> error "evalR: impossible pattern needlessly required"
  SliceR i n d -> case rshape c of
    n' :$: rest ->
      assert (n' == n `blame` (n', n)) $
      evalR s (rconcat [ rzero (i :$: rest)
                       , c
                       , rzero (lengthDelta d - i - n :$: rest) ])
              d
    ZSR -> error "evalR: impossible pattern needlessly required"
  ReverseR d -> evalR s (rreverse c) d
  TransposeR perm d ->
    let permR = permInverse perm
    in evalR s (rtranspose permR c) d
  ReshapeR _sh d -> evalR s (rreshape (shapeDelta d) c) d
  GatherR _sh d f -> evalR s (rscatter (shapeDelta d) c f) d

  CastR d -> evalRRuntimeSpecialized s (rcast c) d

  RFromS (SFromR d) -> evalR s c d  -- no information lost, so no checks
  RFromS @sh d | Dict <- lemKnownNatRank (knownShS @sh) -> evalR s (sfromR c) d
  -- We don't simplify deltas systematically elsewhere, so this is placed here.
  RFromH (HToH hv) i -> evalDynamic s (DynamicRanked c, hv V.! i)
  -- violates sharing: RFromH (ShareH _ (HToH hv)) i -> ...
  RFromH d i ->
    let cs = V.map dynamicFromVoid $ shapeDeltaH d
        ci = DynamicRanked c
    in assert (dynamicsMatch (cs V.! i) ci) $
       evalR s (HVectorPseudoTensor $ dmkHVector $ cs V.// [(i, ci)]) d
        -- should be used only with small vectors or we end up with the same
        -- problem of summing a lot of one-hots as in indexing

  ZeroS -> s
  InputS i -> let cs = MTKS c
              in s {iMap = DMap.adjust (addInterpretationTargetM cs) i
                           $ iMap s}
  ScaleS k d -> evalR s (k * c) d
  AddS d e -> let cShared = sshare c
              in evalR (evalR s cShared d) cShared e
  ShareS n d ->
    assert (case d of
              ZeroS -> False
              ShareS{} -> False  -- wasteful and nonsensical
              _ -> True)
    $ let cs = DTKS c
      in case DMap.lookup n $ nMap s of
        Just _ ->
          s {dMap = DMap.adjust (addInterpretationTargetD cs) n $ dMap s}
        Nothing ->
          s { nMap = DMap.insert n d $ nMap s
            , dMap = DMap.insert n cs $ dMap s }

  IndexS @sh1 @sh d ix ->
    gcastWith (unsafeCoerce Refl
               :: Sh.Drop (X.Rank sh1) (sh1 X.++ sh) :~: sh) $
    gcastWith (unsafeCoerce Refl
               :: Sh.Take (X.Rank sh1) (sh1 X.++ sh) :~: sh1) $
    withListSh (Proxy @sh1) $ \(_ :: IShR rankSh1) ->
    gcastWith (unsafeCoerce Refl :: rankSh1 :~: X.Rank sh1) $
    evalR s (sscatter @_ @_ @'[] @(X.Rank sh1) c (const ix)) d
    -- equivalent: evalR s (updateNR (replicate0NR sh 0) [(ix, c)]) d
  SumS d -> evalR s (sreplicate c) d
  Sum0S d -> evalR s (sreplicate0N c) d
  Dot0S v vd -> evalR s (v * sreplicate0N c) vd
    -- too slow: evalR s (smap0N (* (sscalar c)) v) vd
  ScatterS d f -> evalR s (sgather c f) d

  FromVectorS ld ->
    let cShared = sshare c
    in V.ifoldl' (\ !s2 i d2 ->
         evalR s2 (cShared !$ (fromIntegral i :.$ ZIS)) d2) s ld
  ReplicateS d -> evalR s (ssum c) d
  AppendS @_ @_ @m d e ->
    let cShared = sshare c
        s2 = evalR s (sslice (Proxy @0) Proxy cShared) d
    in evalR s2 (sslice (Proxy @m) Proxy cShared) e
  SliceS @_ @i d ->
    evalR s (sappend @_ @_ @i (srepl 0) (sappend c (srepl 0))) d
  ReverseS d -> evalR s (sreverse c) d
  TransposeS @perm @sh2 perm d ->
    withShapeP (backpermutePrefixList (Permutation.permToList' perm)
                                      (shapeT @sh2)) $ \(Proxy @shp) ->
    gcastWith (unsafeCoerce Refl :: Permutation.PermutePrefix perm sh2 :~: shp) $
    Permutation.permInverse perm $ \(permRev :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerce Refl
                   :: Permutation.PermutePrefix permR (Permutation.PermutePrefix perm sh2) :~: sh2)
        $ gcastWith (unsafeCoerce Refl
                     :: X.Rank (Permutation.PermutePrefix perm sh2) :~: X.Rank sh2)
        $ gcastWith (unsafeCoerce Refl
                     :: X.Rank permR :~: X.Rank perm)
        $ evalR s (stranspose permRev c) d
  ReshapeS d -> evalR s (sreshape c) d
  GatherS d f -> evalR s (sscatter c f) d
  CastS d -> evalSRuntimeSpecialized s (scast c) d
  SFromR @sh (RFromS @sh2 d) ->
    case sameShape @sh @sh2 of
      Just Refl -> evalR s c d
      _ -> error "evalR: different shapes in SFromR(RFromS)"
  SFromR d -> evalR s (rfromS c) d
  SFromH (HToH hv) i -> evalDynamic s (DynamicShaped c, hv V.! i)
  SFromH d i ->
    let cs = V.map dynamicFromVoid $ shapeDeltaH d
        ci = DynamicShaped c
    in assert (dynamicsMatch (cs V.! i) ci) $
       evalR s (HVectorPseudoTensor $ dmkHVector $ cs V.// [(i, ci)]) d

  ShareH n d ->
    assert (case d of
              ShareH{} -> False  -- wasteful and nonsensical
              _ -> True)
    $ let cShared = dshare $ unHVectorPseudoTensor c
          cs = DTKUntyped cShared
      in case DMap.lookup n $ nMap s of
        Just{} ->
          s {dMap = DMap.adjust (addInterpretationTargetD cs) n $ dMap s}
        Nothing ->
          s { nMap = DMap.insert n d $ nMap s
            , dMap = DMap.insert n cs $ dMap s }
  HToH v -> evalHVector s (dunHVector $ dshare $ unHVectorPseudoTensor c) v
  MapAccumR k accShs bShs eShs q es _df rf acc0' es' ->
    let accLen = V.length accShs
        bLen = V.length bShs
        (c0, crest) = V.splitAt accLen $ dunHVector
                      $ dshare $ unHVectorPseudoTensor c
        dacc_desUnshared =
          dmapAccumL (Proxy @ranked)
                     k accShs eShs (bShs V.++ accShs V.++ eShs)
                     (\dx db_acc_e ->
                        let (db, acc_eH) = V.splitAt bLen db_acc_e
                            dx_db = HVectorPseudoTensor $ dmkHVector
                                    $ dx V.++ db
                            acc_e = HVectorPseudoTensor $ dmkHVector acc_eH
                        in unHVectorPseudoTensor
                           $ unHFun rf (dx_db, acc_e))
                     (dmkHVector c0)
                     (dmkHVector $ V.concat [crest, q, es])
        dacc_des = dunHVector $ dshare dacc_desUnshared
        (dacc, des) = V.splitAt accLen dacc_des
        s2 = evalHVector s dacc acc0'
    in evalHVector s2 des es'
  MapAccumL k accShs bShs eShs q es _df rf acc0' es' ->
    let accLen = V.length accShs
        bLen = V.length bShs
        (c0, crest) = V.splitAt accLen $ dunHVector
                      $ dshare $ unHVectorPseudoTensor c
        dacc_desUnshared =
          dmapAccumR (Proxy @ranked)
                     k accShs eShs (bShs V.++ accShs V.++ eShs)
                     (\dx db_acc_e ->
                        let (db, acc_eH) = V.splitAt bLen db_acc_e
                            dx_db = HVectorPseudoTensor $ dmkHVector
                                    $ dx V.++ db
                            acc_e = HVectorPseudoTensor $ dmkHVector acc_eH
                        in unHVectorPseudoTensor
                           $ unHFun rf (dx_db, acc_e))
                     (dmkHVector c0)
                     (dmkHVector $ V.concat [crest, q, es])
        dacc_des = dunHVector $ dshare dacc_desUnshared
        (dacc, des) = V.splitAt accLen dacc_des
        s2 = evalHVector s dacc acc0'
    in evalHVector s2 des es'

evalDynamic
  :: ADReady ranked
  => EvalState ranked
  -> (DynamicTensor ranked, DynamicTensor (DeltaR ranked))
  -> EvalState ranked
evalDynamic !s3 (t, DynamicRanked d2) = evalR s3 (rfromD t) $ unDeltaR d2
evalDynamic s3 (t, DynamicShaped d2) = evalR s3 (sfromD t) $ unDeltaS d2
evalDynamic s3 (t, DynamicRankedDummy @r @sh _ _) =
  withListSh (Proxy @sh) $ \sh2 ->
    evalR s3 (rfromD @r t) (ZeroR sh2)
evalDynamic s3 (t, DynamicShapedDummy @r @sh _ _) =
  evalR @(TKS r sh) s3 (sfromD t) ZeroS

evalHVector
  :: ADReady ranked
  => EvalState ranked -> HVector ranked -> HVector (DeltaR ranked)
  -> EvalState ranked
evalHVector s as as' = V.foldl' evalDynamic s $ V.zip as as'

evalFromnMap :: ADReady ranked
             => EvalState ranked -> EvalState ranked
evalFromnMap s@EvalState{nMap, dMap} =
  -- We discharge the non-vector cases before the vector ones, because
  -- the latter tend to create and store more cases and so enlarge
  -- the working set of cases.
  case DMap.maxViewWithKey nMap of
    Just (n@(NodeId @_ @y _) :=> d, nMap2) ->
      let s2 = s {nMap = nMap2}
          errorMissing :: a
          errorMissing = error $ "evalFromnMap: missing cotangent " ++ show n
          s3 = case stensorKind @y of
            STKR{} -> case DMap.lookup n dMap of
              Just (DTKR c) -> evalRRuntimeSpecialized s2 c d
              Nothing -> errorMissing
            STKS{} -> case DMap.lookup n dMap of
              Just (DTKS c) -> evalSRuntimeSpecialized s2 c d
              Nothing -> errorMissing
            STKProduct{} -> error "TODO" {- case DMap.lookup n dMap of
              Just (DTKProduct c1 c2) -> evalR s2 (c1, c2) d
              Nothing -> errorMissing -}
            STKUntyped -> case DMap.lookup n dMap of
              Just (DTKUntyped c) -> evalR s2 (HVectorPseudoTensor c) d
              Nothing -> errorMissing
      in evalFromnMap s3
    Nothing -> s  -- loop ends

{-
        -- The general case is given as the last one below,
        -- but for a few constructors it's faster to inline @evalR@ instead.
        -- BTW, such an optimization doesn't really belong in the simplified
        -- horde-ad and no consistent benefit should be expected here.
        Index0 ZeroR{} _ _ -> s  -- shortcut
        Index0 (InputR i) ixs' sh ->
          let ixs = indexToList ixs'
              f v = if isTensorDummy v
                    then treplicate0ND sh 0 `OD.update` [(ixs, c)]
                    else v `OD.update` [(ixs, v `rindex0D` ixs + c)]
          in s {iMap = DMap.adjust f i $ iMap s}
        Index0 (ShareR n d) ixs' sh ->
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
            _ -> error "evalFromnMap: corrupted nMap"
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
-- This mimics 'buildFinMaps', but in reverse. Perhaps this can be
-- simplified, but the obvious simplest formulation does not honour sharing
-- and evaluates shared subexpressions repeatedly, so this state-passing
-- formulation is adopted.
fwdDynamic
  :: forall ranked. ADReady ranked
  => Int -> HVector ranked
  -> EvalState ranked
  -> DynamicTensor (DeltaR ranked)
  -> (EvalState ranked, DynamicTensor ranked)
fwdDynamic dimR params s (DynamicRanked d) =
  second DynamicRanked $ fwdR dimR params s (unDeltaR d)
fwdDynamic dimR params s (DynamicShaped d) =
  second DynamicShaped $ fwdR dimR params s (unDeltaS d)
fwdDynamic dimR params s (DynamicRankedDummy @r @sh _ _) =
  withListSh (Proxy @sh) $ \sh2 ->
    second (DynamicRanked @r) $ fwdR dimR params s (ZeroR sh2)
fwdDynamic dimR params s (DynamicShapedDummy @r @sh _ _) =
  second (DynamicShaped @r @sh) $ fwdR dimR params s ZeroS

fwdHVector
  :: forall ranked. ADReady ranked
  => Int -> HVector ranked
  -> EvalState ranked
  -> HVector (DeltaR ranked)
  -> (EvalState ranked, HVector ranked)
fwdHVector dimR params = mapAccumL (fwdDynamic dimR params)

fwdR
  :: forall ranked y. ADReady ranked
  => Int -> HVector ranked -> EvalState ranked -> Delta ranked y
  -> (EvalState ranked, InterpretationTarget ranked y)
fwdR dimR params s = \case
  TupleG d1 d2 -> let (s2, t) = fwdR dimR params s d1
                      (s3, u) = fwdR dimR params s2 d2
                  in (s3, (t, u))
  Project1G d -> let (s2, v) = fwdR dimR params s d
                 in (s2, fst v)
  Project2G d -> let (s2, v) = fwdR dimR params s d
                 in (s2, snd v)

  ZeroR sh -> (s, rzero sh)
  InputR @_ @r @n _ (InputId i) ->
    if i < dimR
    then case params V.! i of
      DynamicRanked @r2 @n2 e -> case sameNat (Proxy @n2) (Proxy @n) of
        Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> (s, e)
          _ -> error "fwdR: scalar mismatch"
        _ -> error "fwdR: rank mismatch"
      DynamicShaped{} -> error "fwdR: DynamicShaped"
      DynamicRankedDummy{} -> error "fwdR: DynamicRankedDummy"
      DynamicShapedDummy{} -> error "fwdR: DynamicShapedDummy"
    else error "fwdR': wrong index for an input"
  ScaleR k d -> second (* k) $ fwdR dimR params s d
  AddR d e -> let (s2, t) = fwdR dimR params s d
                  (s3, u) = fwdR dimR params s2 e
              in (s3, t + u)
  ShareR n d ->
    case DMap.lookup n $ dMap s of
      Just (DTKR e) -> (s, e)
      Nothing ->
        let (s2, cRaw) = fwdR dimR params s d
            cShared = rshare cRaw
            s3 = s2 {dMap = DMap.insert n (DTKR cShared) (dMap s2)}
        in (s3, cShared)

  IndexR d ix -> second (`rindex` ix) $ fwdR dimR params s d
  SumR d -> second rsum $ fwdR dimR params s d
  Sum0R ZeroR{} -> (s, 0)
  Sum0R d -> second rsum0 $ fwdR dimR params s d
  Dot0R _ ZeroR{} -> (s, 0)
  Dot0R v d -> second (rdot0 v) $ fwdR dimR params s d
  ScatterR sh d f ->
    let (s2, t) = fwdR dimR params s d
    in (s2, rscatter sh t f)

  FromVectorR lsd ->
    let (s2, l) = mapAccumL (fwdR dimR params) s lsd
    in (s2, rfromVector l)
  ReplicateR n d ->
    let (s2, t) = fwdR dimR params s d
    in (s2, rreplicate n t)
  AppendR d e ->
    let (s2, t) = fwdR dimR params s d
        (s3, u) = fwdR dimR params s2 e
    in (s3, rappend t u)
  SliceR i n d -> second (rslice i n) $ fwdR dimR params s d
  ReverseR d -> second rreverse $ fwdR dimR params s d
  TransposeR perm d -> second (rtranspose perm) $ fwdR dimR params s d
  ReshapeR sh d -> second (rreshape sh) $ fwdR dimR params s d
  GatherR sh d f ->
    let (s2, t) = fwdR dimR params s d
    in (s2, rgather sh t f)
  CastR d ->
    second rcast $ fwdR dimR params s d

  RFromS (SFromR d) ->
    fwdR dimR params s d  -- no information lost, so no checks
  RFromS d -> second rfromS $ fwdR dimR params s d
  RFromH d i -> let (s2, v) = fwdR dimR params s d
                in (s2, rfromD $ dunHVector (unHVectorPseudoTensor v) V.! i)

  ZeroS -> (s, srepl 0)
  InputS @_ @r @sh (InputId i) ->
    if i < dimR
    then case params V.! i of
      DynamicRanked{} -> error "fwdR: DynamicRanked"
      DynamicShaped @r2 @sh2 e -> case sameShape @sh2 @sh of
        Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> (s, e)
          _ -> error "fwdR: scalar mismatch"
        _ -> error "fwdR: shape mismatch"
      DynamicRankedDummy{} -> error "fwdR: DynamicRankedDummy"
      DynamicShapedDummy{} -> error "fwdR: DynamicShapedDummy"
    else error "fwdR: wrong index for an input"
  ScaleS k d -> second (* k) $ fwdR dimR params s d
  AddS d e -> let (s2, t) = fwdR dimR params s d
                  (s3, u) = fwdR dimR params s2 e
              in (s3, t + u)
  ShareS n d ->
    case DMap.lookup n $ dMap s of
      Just (DTKS e) -> (s, e)
      Nothing ->
        let (s2, cRaw) = fwdR dimR params s d
            cShared = sshare cRaw
            s3 = s2 {dMap = DMap.insert n (DTKS cShared) (dMap s2)}
        in (s3, cShared)

  IndexS d ix -> second (`sindex` ix) $ fwdR dimR params s d
  SumS d -> second ssum $ fwdR dimR params s d
  Sum0S ZeroS -> (s, srepl 0)
  Sum0S d -> second ssum0 $ fwdR dimR params s d
  Dot0S _ ZeroS -> (s, srepl 0)
  Dot0S v d -> second (sdot0 v) $ fwdR dimR params s d
  ScatterS d f ->
    let (s2, t) = fwdR dimR params s d
    in (s2, sscatter t f)

  FromVectorS lsd ->
    let (s2, l) = mapAccumL (fwdR dimR params) s lsd
    in (s2, sfromVector l)
  ReplicateS d ->
    let (s2, t) = fwdR dimR params s d
    in (s2, sreplicate t)
  AppendS d e ->
    let (s2, t) = fwdR dimR params s d
        (s3, u) = fwdR dimR params s2 e
    in (s3, sappend t u)
  SliceS @_ @i d -> second (sslice (Proxy @i) Proxy) $ fwdR dimR params s d
  ReverseS d -> second sreverse $ fwdR dimR params s d
  TransposeS perm d -> second (stranspose perm)
                       $ fwdR dimR params s d
  ReshapeS d -> second sreshape $ fwdR dimR params s d
  GatherS d f ->
    let (s2, t) = fwdR dimR params s d
    in (s2, sgather t f)
  CastS d ->
    second scast $ fwdR dimR params s d

  SFromR @sh (RFromS @sh2 d) ->
    case sameShape @sh @sh2 of
      Just Refl -> fwdR dimR params s d
      _ -> error "fwdR: different shapes in SFromR(RFromS)"
  SFromR d -> second sfromR $ fwdR dimR params s d
  SFromH d i -> let (s2, v) = fwdR dimR params s d
                in (s2, sfromD $ dunHVector (unHVectorPseudoTensor v) V.! i)

  ShareH n d ->
    case DMap.lookup n $ dMap s of
      Just (DTKUntyped hv) -> (s, HVectorPseudoTensor hv)
      Nothing ->
        let (s2, cRaw) = fwdR dimR params s d
            cShared = dshare $ unHVectorPseudoTensor cRaw
            s3 = s2 {dMap = DMap.insert n (DTKUntyped cShared) (dMap s2)}
        in (s3, HVectorPseudoTensor cShared)
  HToH v -> second (HVectorPseudoTensor . dmkHVector)
            $ fwdHVector dimR params s v
  MapAccumR k accShs bShs eShs q es df _rf acc0' es' ->
    let (s2, cacc0) = fwdHVector dimR params s acc0'
        (s3, ces) = fwdHVector dimR params s2 es'
        eLen = V.length eShs
    in (s3, HVectorPseudoTensor
            $ dmapAccumR (Proxy @ranked)
                          k accShs bShs (eShs V.++ accShs V.++ eShs)
                          (\dacc de_acc_e ->
                             let (de, acc_eH) = V.splitAt eLen de_acc_e
                                 acc_e = HVectorPseudoTensor $ dmkHVector acc_eH
                                 dacc_de = HVectorPseudoTensor $ dmkHVector
                                           $ dacc V.++ de
                             in unHVectorPseudoTensor
                                $ unHFun df (dacc_de, acc_e))
                          (dmkHVector cacc0)
                          (dmkHVector $ V.concat [ces, q, es]))
  MapAccumL k accShs bShs eShs q es df _rf acc0' es' ->
    let (s2, cacc0) = fwdHVector dimR params s acc0'
        (s3, ces) = fwdHVector dimR params s2 es'
        eLen = V.length eShs
    in (s3, HVectorPseudoTensor
            $ dmapAccumL (Proxy @ranked)
                          k accShs bShs (eShs V.++ accShs V.++ eShs)
                          (\dacc de_acc_e ->
                             let (de, acc_eH) = V.splitAt eLen de_acc_e
                                 acc_e = HVectorPseudoTensor $ dmkHVector acc_eH
                                 dacc_de = HVectorPseudoTensor $ dmkHVector
                                           $ dacc V.++ de
                             in unHVectorPseudoTensor
                                $ unHFun df (dacc_de, acc_e))
                          (dmkHVector cacc0)
                          (dmkHVector $ V.concat [ces, q, es]))
