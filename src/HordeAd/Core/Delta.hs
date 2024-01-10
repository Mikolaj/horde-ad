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
module HordeAd.Core.Delta
  ( -- * Abstract syntax trees of the delta expressions
    DeltaR (..), DeltaS (..)
  , -- * Delta expression identifiers
    NodeId (..), InputId, toInputId
  , -- * Evaluation of the delta expressions
    DualPart(..), DeltaDt (..)
  , -- * Miscellaneous
    mapDomainsDeltaR11, mapDomainsDeltaS11kk
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (liftM2)
import           Control.Monad.ST.Strict (ST, runST)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Int (Int64)
import           Data.Kind (Constraint, Type)
import           Data.List (foldl', mapAccumR, sort, transpose)
import           Data.List.Index (ifoldl')
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy (Proxy))
import           Data.STRef (newSTRef, readSTRef, writeSTRef)
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.Show (showSpace)
import           GHC.TypeLits (KnownNat, Nat, sameNat, type (+), type (<=))
import           Text.Show.Functions ()
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (sameShape, trustMeThisIsAPermutation)
import           HordeAd.Util.ShapedList (ShapedList (..))
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex

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
type role DeltaR nominal nominal nominal
data DeltaR :: RankedTensorType -> RankedTensorType where
  ZeroR :: ShapeInt n -> DeltaR ranked r n
    -- ^ the shape is required for @shapeDelta@ and forward derivative
  InputR :: forall ranked r n.
            ShapeInt n -> InputId ranked -> DeltaR ranked r n
  ScaleR :: ranked r n -> DeltaR ranked r n -> DeltaR ranked r n
  AddR :: DeltaR ranked r n -> DeltaR ranked r n
       -> DeltaR ranked r n
  LetR :: NodeId ranked -> DeltaR ranked r n
       -> DeltaR ranked r n

  IndexR :: (KnownNat n, KnownNat m)
         => DeltaR ranked r (m + n) -> IndexOf ranked m
         -> DeltaR ranked r n
    -- ^ The sub-tensor at the given index. The given shape is of the
    -- large tensor. If index is out of bounds, the result is defined and is 0.
  SumR :: KnownNat n
       => DeltaR ranked r (1 + n) -> DeltaR ranked r n
  Sum0R :: KnownNat n
        => DeltaR ranked r n -> DeltaR ranked r 0
  Dot0R :: KnownNat n
        => ranked r n -> DeltaR ranked r n -> DeltaR ranked r 0
  ScatterR :: (KnownNat m, KnownNat p, KnownNat n)
           => ShapeInt (p + n) -> DeltaR ranked r (m + n)
           -> (IndexOf ranked m -> IndexOf ranked p)
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
             => Int -> DeltaR ranked r n
             -> DeltaR ranked r (1 + n)
    -- ^ Copy the given tensor along the new, outermost dimension.
  AppendR :: KnownNat n
          => DeltaR ranked r (1 + n)
          -> DeltaR ranked r (1 + n)
          -> DeltaR ranked r (1 + n)
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
  SliceR :: KnownNat n
         => Int -> Int -> DeltaR ranked r (1 + n)
         -> DeltaR ranked r (1 + n)
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
  ReverseR :: KnownNat n
           => DeltaR ranked r (1 + n) -> DeltaR ranked r (1 + n)
    -- ^ Reverse elements of the outermost dimension.
  TransposeR :: KnownNat n
             => Permutation -> DeltaR ranked r n
             -> DeltaR ranked r n
    -- ^ Transpose according to the permutation.
  ReshapeR :: (KnownNat n, KnownNat m)
           => ShapeInt m -> DeltaR ranked r n
           -> DeltaR ranked r m
    -- ^ Change the shape of the tensor to the given one.
  GatherR :: (KnownNat m, KnownNat p, KnownNat n)
          => ShapeInt (m + n) -> DeltaR ranked r (p + n)
          -> (IndexOf ranked m -> IndexOf ranked p)
          -> DeltaR ranked r (m + n)
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @Gather1 (const Z) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @GatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for Gather1; fix.
  FoldR :: (GoodScalar rm, KnownNat m)
        => ranked rn (1 + n) -> ranked rm (1 + m)
        -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                -> f rn n)
        -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> DomainsOf f)
        -> DeltaR ranked rn n
        -> DeltaR ranked rm (1 + m)
        -> DeltaR ranked rn n
    -- ^ Fold over the outermost dimension of a tensor.
  FoldRC :: (GoodScalar rm, KnownNat m)
         => ranked rn (1 + n) -> ranked rm (1 + m)
         -> (ranked rn n -> (ranked rm m, ranked rn n, ranked rm m)
             -> ranked rn n)
         -> (ranked rn n -> (ranked rn n, ranked rm m)
             -> (ranked rn n, ranked rm m))
         -> DeltaR ranked rn n
         -> DeltaR ranked rm (1 + m)
         -> DeltaR ranked rn n
  FoldDR :: DomainsOD
         -> ranked rn (1 + n)
         -> Domains ranked  -- one rank higher than the Domains above
         -> (forall f. ADReady f
             => f rn n -> DomainsOf f -> f rn n -> DomainsOf f
             -> f rn n)
         -> (forall f. ADReady f
             => f rn n -> f rn n -> DomainsOf f
             -> DomainsOf f)
         -> DeltaR ranked rn n
         -> Domains (DeltaR ranked)  -- one rank higher
         -> DeltaR ranked rn n
  FoldDRC :: DomainsOD
          -> ranked rn (1 + n)
          -> Domains ranked
          -> (ranked rn n -> DomainsOf ranked -> ranked rn n -> DomainsOf ranked
              -> ranked rn n)
          -> (ranked rn n -> ranked rn n -> DomainsOf ranked
              -> DomainsOf ranked)
          -> DeltaR ranked rn n
          -> Domains (DeltaR ranked)
          -> DeltaR ranked rn n
  ScanR :: (GoodScalar rm, KnownNat m)
        => ranked rn (1 + n) -> ranked rm (1 + m)
        -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                -> f rn n)
        -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> DomainsOf f)
        -> DeltaR ranked rn n
        -> DeltaR ranked rm (1 + m)
        -> DeltaR ranked rn (1 + n)
  ScanDR :: DomainsOD
         -> ranked rn (1 + n)
         -> Domains ranked  -- one rank higher than the Domains above
         -> (forall f. ADReady f
             => f rn n -> DomainsOf f -> f rn n -> DomainsOf f
             -> f rn n)
         -> (forall f. ADReady f
             => f rn n -> f rn n -> DomainsOf f
             -> DomainsOf f)
         -> DeltaR ranked rn n
         -> Domains (DeltaR ranked)  -- one rank higher
         -> DeltaR ranked rn (1 + n)
  CastR :: (GoodScalar r1, RealFrac r1, RealFrac r2)
        => DeltaR ranked r1 n -> DeltaR ranked r2 n
  SToR :: forall sh r ranked. Sh.Shape sh
       => DeltaS (ShapedOf ranked) r sh
       -> DeltaR ranked r (Sh.Rank sh)

{- Fails due to @forall f@. Replaced by a manually fixed version at the end
   of this file.
deriving instance ( KnownNat n0, GoodScalar r0
                  , Show (IntOf ranked)
                  , Show (IntOf (ShapedOf ranked))
                  , CRanked ranked Show
                  , CShaped (ShapedOf ranked) Show
                  , CShaped (DeltaS (ShapedOf ranked)) Show )
                  => Show (DeltaR ranked r0 n0)
-}

-- | This is the grammar of delta-expressions that record derivatives
-- of shaped tensors.
type role DeltaS nominal nominal nominal
data DeltaS :: ShapedTensorType -> ShapedTensorType where
  ZeroS :: DeltaS shaped r sh
  InputS :: InputId (RankedOf shaped) -> DeltaS shaped r sh
  ScaleS :: shaped r sh -> DeltaS shaped r sh
         -> DeltaS shaped r sh
  AddS :: DeltaS shaped r sh -> DeltaS shaped r sh
       -> DeltaS shaped r sh
  LetS :: NodeId (RankedOf shaped) -> DeltaS shaped r sh
       -> DeltaS shaped r sh

  IndexS :: (Sh.Shape sh1, Sh.Shape (sh1 Sh.++ sh2))
         => DeltaS shaped r (sh1 Sh.++ sh2)
         -> IndexSh shaped sh1
         -> DeltaS shaped r sh2
    -- ^ The sub-tensor at the given index.
    -- If index is out of bounds, the result is defined and is 0.
  SumS :: KnownNat n
       => DeltaS shaped r (n ': sh) -> DeltaS shaped r sh
  Sum0S :: (Sh.Shape sh, KnownNat (Sh.Size sh))
        => DeltaS shaped r sh -> DeltaS shaped r '[]
  Dot0S :: (Sh.Shape sh, KnownNat (Sh.Size sh))
        => shaped r sh -> DeltaS shaped r sh
        -> DeltaS shaped r '[]
  ScatterS :: forall shaped r sh2 p sh.
              ( Sh.Shape sh2, Sh.Shape (Sh.Take p sh), Sh.Shape (Sh.Drop p sh)
              , Sh.Shape (sh2 Sh.++ Sh.Drop p sh) )
           => DeltaS shaped r (sh2 Sh.++ Sh.Drop p sh)
           -> (IndexSh shaped sh2
               -> IndexSh shaped (Sh.Take p sh))
           -> DeltaS shaped r sh
    -- ^ Build a tensor by adding up tensors of rank @n@ taken from
    -- the third argument and inserted in a zero tensor
    -- at indexes of length @p@. Indexes of length 0 insert tensors trivially,
    -- so that, e.g, @Scatter1 5 (const Z) (Replicate0R [5] d) []@ is equivalent
    -- to @5 * d@. If an index of length @p@ is out of bounds, no tensor
    -- is added at such an index (and similarly in @ScatterN@).
    -- The semantics of the operation permits index out of bounds
    -- and then no tensors is added at such an index.
    -- TODO: this is a haddock for Scatter1; fix.

  FromListS :: (Sh.Shape sh, KnownNat n)
            => [DeltaS shaped r sh] -> DeltaS shaped r (n ': sh)
    -- ^ Create a tensor from a list treated as the outermost dimension.
  FromVectorS :: (Sh.Shape sh, KnownNat n)
              => Data.Vector.Vector (DeltaS shaped r sh)
              -> DeltaS shaped r (n ': sh)
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  ReplicateS :: forall shaped r n sh.
                (Sh.Shape sh, KnownNat n)
             => DeltaS shaped r sh -> DeltaS shaped r (n ': sh)
    -- ^ Copy the given tensor along the new, outermost dimension.
  AppendS :: forall shaped r m n sh.
             (KnownNat m, KnownNat n, Sh.Shape sh)
          => DeltaS shaped r (m ': sh)
          -> DeltaS shaped r (n ': sh)
          -> DeltaS shaped r ((m + n) ': sh)
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
    -- The integer argument is the outermost size of the first array.
  SliceS :: forall shaped i n k r sh.
            (KnownNat i, KnownNat n, KnownNat k, Sh.Shape sh)
         => DeltaS shaped r (i + n + k ': sh)
         -> DeltaS shaped r (n ': sh)
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
    -- The last argument is the outermost size of the argument array.
  ReverseS :: (Sh.Shape sh, KnownNat n)
           => DeltaS shaped r (n ': sh)
           -> DeltaS shaped r (n ': sh)
    -- ^ Reverse elements of the outermost dimension.
  TransposeS :: forall shaped perm r sh.
                ( OS.Permutation perm, Sh.Shape perm, Sh.Shape sh
                , KnownNat (Sh.Rank sh), Sh.Rank perm <= Sh.Rank sh )
             => DeltaS shaped r sh
             -> DeltaS shaped r (Sh.Permute perm sh)
    -- ^ Transpose according to the permutation.
  ReshapeS :: (Sh.Shape sh, Sh.Size sh ~ Sh.Size sh2)
           => DeltaS shaped r sh
           -> DeltaS shaped r sh2
    -- ^ Change the shape of the tensor from the first to the second.
  GatherS :: forall shaped r sh2 p sh.
             ( Sh.Shape sh2, Sh.Shape sh
             , Sh.Shape (Sh.Take p sh), Sh.Shape (Sh.Drop p sh) )
          => DeltaS shaped r sh
          -> (IndexSh shaped sh2
              -> IndexSh shaped (Sh.Take p sh))
          -> DeltaS shaped r (sh2 Sh.++ Sh.Drop p sh)
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @Gather1 (const Z) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @GatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for Gather1; fix.
  FoldS :: (GoodScalar rm, Sh.Shape shm, KnownNat k)
        => shaped rn (1 + k ': sh) -> shaped rm (k ': shm)
        -> (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh -> f rm shm
                                 -> f rn sh)
        -> (forall f. ADReadyS f => f rn sh -> f rn sh -> f rm shm
                                 -> DomainsOf (RankedOf f))
        -> DeltaS shaped rn sh
        -> DeltaS shaped rm (k ': shm)
        -> DeltaS shaped rn sh
  FoldSC :: (GoodScalar rm, Sh.Shape shm, KnownNat k)
        => shaped rn (1 + k ': sh) -> shaped rm (k ': shm)
        -> (shaped rn sh -> (shaped rm shm, shaped rn sh, shaped rm shm)
            -> shaped rn sh)
        -> (shaped rn sh -> (shaped rn sh, shaped rm shm)
            -> (shaped rn sh, shaped rm shm))
        -> DeltaS shaped rn sh
        -> DeltaS shaped rm (k ': shm)
        -> DeltaS shaped rn sh
  FoldDS :: KnownNat k
         => DomainsOD
         -> shaped rn (1 + k ': sh)
         -> Domains (RankedOf shaped)  -- one rank higher than the Domains above
         -> (forall f. ADReadyS f
             => f rn sh -> DomainsOf (RankedOf f) -> f rn sh
             -> DomainsOf (RankedOf f)
             -> f rn sh)
         -> (forall f. ADReadyS f
             => f rn sh -> f rn sh -> DomainsOf (RankedOf f)
             -> DomainsOf (RankedOf f))
         -> DeltaS shaped rn sh
         -> Domains (DeltaR (RankedOf shaped))
         -> DeltaS shaped rn sh
  FoldDSC :: KnownNat k
          => DomainsOD
          -> shaped rn (1 + k ': sh)
          -> Domains (RankedOf shaped)
          -> (shaped rn sh -> DomainsOf (RankedOf shaped) -> shaped rn sh
              -> DomainsOf (RankedOf shaped)
              -> shaped rn sh)
          -> (shaped rn sh -> shaped rn sh -> DomainsOf (RankedOf shaped)
              -> DomainsOf (RankedOf shaped))
          -> DeltaS shaped rn sh
          -> Domains (DeltaR (RankedOf shaped))
          -> DeltaS shaped rn sh
  ScanS :: (GoodScalar rm, Sh.Shape shm, KnownNat k, Sh.Shape sh)
        => shaped rn (1 + k ': sh) -> shaped rm (k ': shm)
        -> (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh -> f rm shm
                                 -> f rn sh)
        -> (forall f. ADReadyS f => f rn sh -> f rn sh -> f rm shm
                                 -> DomainsOf (RankedOf f))
        -> DeltaS shaped rn sh
        -> DeltaS shaped rm (k ': shm)
        -> DeltaS shaped rn (1 + k ': sh)
  ScanDS :: (Sh.Shape sh, KnownNat k)
         => DomainsOD
         -> shaped rn (1 + k ': sh)
         -> Domains (RankedOf shaped)  -- one rank higher than the Domains above
         -> (forall f. ADReadyS f
             => f rn sh -> DomainsOf (RankedOf f) -> f rn sh
             -> DomainsOf (RankedOf f)
             -> f rn sh)
         -> (forall f. ADReadyS f
             => f rn sh -> f rn sh -> DomainsOf (RankedOf f)
             -> DomainsOf (RankedOf f))
         -> DeltaS shaped rn sh
         -> Domains (DeltaR (RankedOf shaped))
         -> DeltaS shaped rn (1 + k ': sh)
  CastS :: (GoodScalar r1, RealFrac r1, RealFrac r2)
        => DeltaS shaped r1 sh -> DeltaS shaped r2 sh
  RToS :: forall sh r shaped. KnownNat (Sh.Rank sh)
       => DeltaR (RankedOf shaped) r (Sh.Rank sh)
       -> DeltaS shaped r sh

{- Fails due to @forall f@. Replaced by a manually fixed version at the end
   of this file.
deriving instance ( Sh.Shape sh0, GoodScalar r0
                  , Show (IntOf (RankedOf shaped))
                  , Show (IntOf shaped)
                  , CRanked (RankedOf shaped) Show
                  , CShaped shaped Show
                  , CRanked (DeltaR (RankedOf shaped)) Show )
                  => Show (DeltaS shaped r0 sh0)
-}

-- This is needed for the Show instances due to Domains (Delta...)
-- referring to ShapedOf (Delta..).
type instance RankedOf (DeltaS shaped) = DeltaR (RankedOf shaped)

type instance ShapedOf (DeltaR ranked) = DeltaS (ShapedOf ranked)

shapeDelta :: forall ranked r n.
              ( GoodScalar r, KnownNat n
              , RankedTensor ranked, ShapedTensor (ShapedOf ranked) )
           => DeltaR ranked r n -> ShapeInt n
shapeDelta = \case
  ZeroR sh -> sh
  InputR sh _ -> sh
  ScaleR _ d -> shapeDelta d
  AddR d _ -> shapeDelta d
  LetR _ d -> shapeDelta d
  IndexR d _ -> dropShape (shapeDelta d)
  SumR d -> tailShape (shapeDelta d)
  Sum0R{} -> ZS
  Dot0R{} -> ZS
  ScatterR sh _ _ -> sh
  FromListR l -> case l of
    [] -> case sameNat (Proxy @n) (Proxy @1) of
      Just Refl -> singletonShape 0  -- the only case where we can guess sh
      _ -> error "shapeDelta: FromListR with no arguments"
    d : _ -> length l :$ shapeDelta d
  FromVectorR l -> case V.toList l of
    [] -> case sameNat (Proxy @n) (Proxy @1) of
      Just Refl -> singletonShape 0  -- the only case where we can guess sh
      _ -> error "shapeDelta: FromListR with no arguments"
    d : _ -> length l :$ shapeDelta d
  ReplicateR n d -> n :$ shapeDelta d
  AppendR x y -> case shapeDelta x of
    ZS -> error "shapeDelta: impossible pattern needlessly required"
    xi :$ xsh -> case shapeDelta y of
      ZS -> error "shapeDelta: impossible pattern needlessly required"
      yi :$ _ -> xi + yi :$ xsh
  SliceR _ n d -> n :$ tailShape (shapeDelta d)
  ReverseR d -> shapeDelta d
  TransposeR perm d -> backpermutePrefixShape perm (shapeDelta d)
  ReshapeR sh _ -> sh
  GatherR sh _ _ -> sh
  FoldR _p _as _df _rf x0' _as' -> shapeDelta x0'
  FoldRC _p _as _df _rf x0' _as' -> shapeDelta x0'
  FoldDR _domsOD _p _as _df _rf x0' _as' -> shapeDelta x0'
  FoldDRC _domsOD _p _as _df _rf x0' _as' -> shapeDelta x0'
  ScanR p _as _df _rf _x0' _as' -> rshape p
  ScanDR _domsOD p _as _df _rf _x0' _as' -> rshape p
  CastR d -> shapeDelta d
  SToR @sh _ -> listShapeToShape $ Sh.shapeT @sh

lengthDelta :: forall ranked r n.
               ( GoodScalar r, KnownNat n
               , RankedTensor ranked, ShapedTensor (ShapedOf ranked) )
            => DeltaR ranked r (1 + n) -> Int
lengthDelta d = case shapeDelta d of
  ZS -> error "lengthDelta: impossible pattern needlessly required"
  k :$ _ -> k


-- * Delta expression identifiers

type role NodeId phantom
newtype NodeId (f :: TensorType ty) = NodeId Int
 deriving newtype (Show, Enum)
   -- No Eq instance to limit hacks.

type role InputId phantom
newtype InputId (f :: TensorType ty) = InputId Int
 deriving (Show, Enum)
   -- No Eq instance to limit hacks outside this module.

-- | Wrap non-negative (only!) integers in the `InputId` newtype.
toInputId :: Int -> InputId f
toInputId i = assert (i >= 0) $ InputId i


-- * Evaluation of the delta expressions

type DualPart :: TensorType ty -> Constraint
class DualPart (f :: TensorType ty) where
  -- | The type family that to each basic differentiable type
  -- assigns its delta expression type.
  type Dual f = (result :: TensorType ty) | result -> f
  reverseDervative
    :: (HasSingletonDict y, GoodScalar r)
    => DomainsOD -> f r y -> Maybe (f r y) -> Dual f r y
    -> (AstBindingsD (RankedOf f), Domains (RankedOf f))
  forwardDerivative
    :: (HasSingletonDict y, GoodScalar r)
    => Int -> Dual f r y -> Domains (RankedOf f)
    -> (AstBindingsD (RankedOf f), f r y)

instance (ADReady ranked, RankedOf ranked ~ ranked)
         => DualPart @Nat ranked where
  type Dual ranked = DeltaR ranked
  reverseDervative = gradientDtR
  forwardDerivative = derivativeFromDeltaR

gradientDtR
  :: (KnownNat y, GoodScalar r, ADReady ranked)
  => DomainsOD
  -> ranked r y -> Maybe (ranked r y) -> DeltaR ranked r y
  -> (AstBindingsD ranked, Domains ranked)
gradientDtR !parameters0 value !mdt !deltaTopLevel =
  let dt = fromMaybe (rreplicate0N (rshape value) 1) mdt
      deltaDt = DeltaDtR dt deltaTopLevel
  in gradientFromDelta parameters0 deltaDt
{- TODO: this causes a cyclic dependency:
{-# SPECIALIZE gradientDtR
  :: KnownNat y
  => DomainsOD -> Flip OR.Array Double y -> Maybe (Flip OR.Array Double y)
  -> DeltaR (Flip OR.Array) Double y
  -> (AstBindingsD (Flip OR.Array), Domains (Flip OR.Array) ) #-}
{-# SPECIALIZE gradientDtR
  :: KnownNat y
  => DomainsOD -> AstRanked PrimalSpan Double y
  -> Maybe (AstRanked PrimalSpan Double y)
  -> DeltaR (AstRanked PrimalSpan) Double y
  -> ( AstBindingsD (AstRanked PrimalSpan)
     , Domains (AstRanked PrimalSpan) ) #-}
-}

derivativeFromDeltaR
  :: forall ranked r n.
     (KnownNat n, GoodScalar r, ADReady ranked)
  => Int -> DeltaR ranked r n -> Domains ranked
  -> (AstBindingsD ranked, ranked r n)
derivativeFromDeltaR dim deltaTopLevel ds =
  let dummyZero = rzero $ listShapeToShape $ replicate (valueOf @n) 1
  in case runST $ buildDerivative dim (DeltaDtR dummyZero deltaTopLevel) ds of
    (l, DeltaDtR @_ @n2 res _) -> case sameNat (Proxy @n) (Proxy @n2) of
      Just Refl -> (l, res)
      _ -> error "derivativeFromDeltaR"
    (_, DeltaDtS{}) -> error "derivativeFromDeltaR"

instance ADReadyS shaped
         => DualPart @[Nat] shaped where
  type Dual shaped = DeltaS shaped
  reverseDervative parameters0 _ = gradientDtS parameters0
  forwardDerivative = derivativeFromDeltaS

gradientDtS
  :: forall shaped r y.
     (Sh.Shape y, GoodScalar r, ADReadyS shaped)
  => DomainsOD
  -> Maybe (shaped r y) -> DeltaS shaped r y
  -> (AstBindingsD (RankedOf shaped), Domains (RankedOf shaped))
gradientDtS !parameters0 !mdt !deltaTopLevel =
  let dt = fromMaybe 1 mdt
      deltaDt = DeltaDtS dt deltaTopLevel
  in gradientFromDelta parameters0 deltaDt
{- TODO: this causes a cyclic dependency:
{-# SPECIALIZE gradientDtS
  :: Sh.Shape y
  => DomainsOD -> Maybe (Flip OS.Array Double y)
  -> DeltaS (Flip OS.Array) Double y
  -> (AstBindingsD (Flip OR.Array), Domains (Flip OR.Array)) #-}
{-# SPECIALIZE gradientDtS
  :: Sh.Shape y
  => DomainsOD -> Maybe (AstShaped PrimalSpan Double y)
  -> DeltaS (AstShaped PrimalSpan) Double y
  -> ( AstBindingsD (DynamicTensor (AstShaped PrimalSpan))
     , Domains (DynamicTensor (AstShaped PrimalSpan)) ) #-}
-}

derivativeFromDeltaS
  :: forall shaped r sh.
     (Sh.Shape sh, GoodScalar r, ADReadyS shaped)
  => Int -> DeltaS shaped r sh -> Domains (RankedOf shaped)
  -> (AstBindingsD (RankedOf shaped), shaped r sh)
derivativeFromDeltaS !dim !deltaTopLevel !ds =
  case runST $ buildDerivative dim (DeltaDtS 0 deltaTopLevel) ds of
    (l, DeltaDtS @_ @sh2 res _) -> case sameShape @sh @sh2 of
      Just Refl -> (l, res)
      _ -> error "derivativeFromDeltaS"
    (_, DeltaDtR{}) -> error "derivativeFromDeltaS"

-- | The main input of the differentiation functions:
-- the delta expression to be differentiated and the dt perturbation
-- (small change) of the objective function codomain, for which we compute
-- the gradient.
type role DeltaDt nominal nominal nominal
data DeltaDt :: RankedTensorType -> ShapedTensorType -> Type -> Type where
  DeltaDtR :: forall r n ranked shaped. KnownNat n
           => ranked r n -> DeltaR ranked r n
           -> DeltaDt ranked shaped r
  DeltaDtS :: forall r sh ranked shaped. Sh.Shape sh
           => shaped r sh -> DeltaS shaped r sh
           -> DeltaDt ranked shaped r


-- * Reverse pass, transpose/evaluation of the delta expressions

-- | The state of evaluation. It consists of several maps.
-- The maps indexed by input identifiers and node identifiers
-- eventually store cotangents for their respective nodes.
-- The cotangents are built gradually during the evaluation,
-- by summing cotangent contributions.
--
-- Data invariant:
-- 1. keys nMap == keys dMap
-- 2. key `member` dMap == nMap!key is DeltaBindingR
type role EvalState nominal nominal
data EvalState ranked shaped = EvalState
  { iMap        :: EM.EnumMap (InputId ranked) (DynamicTensor ranked)
      -- ^ eventually, cotangents of objective function inputs
      -- (eventually copied to the vector representing the gradient
      -- of the objective function);
      -- the identifiers need to be contiguous and start at 0
  , dMap        :: EM.EnumMap (NodeId ranked) (DynamicTensor ranked)
      -- ^ eventually, cotangents of non-input subterms indexed
      -- by their node identifiers
  , nMap        :: EM.EnumMap (NodeId ranked) (DeltaBinding ranked shaped)
      -- ^ nodes left to be evaluated
  , astBindings :: AstBindingsD ranked
  }

-- | Nodes left to be evaluated.
-- We can't evaluate them at once, because their other shared copies
-- may still not be processed, so we'd not take advantage of the sharing
-- and not take into account the whole summed context when finally evaluating.
type role DeltaBinding nominal nominal
data DeltaBinding :: RankedTensorType -> ShapedTensorType -> Type where
  DeltaBindingR :: forall n r ranked shaped. (KnownNat n, GoodScalar r)
                => DeltaR ranked r n -> DeltaBinding ranked shaped
  DeltaBindingS :: forall sh r ranked shaped. (Sh.Shape sh, GoodScalar r)
                => DeltaS shaped r sh -> DeltaBinding ranked shaped

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
     ( GoodScalar r, ADReady ranked, shaped ~ ShapedOf ranked)
  => DomainsOD -> DeltaDt ranked shaped r
  -> (AstBindingsD ranked, Domains ranked)
gradientFromDelta !parameters0 !deltaDt =
  -- Create finite maps that hold values associated with inputs
  -- and with (possibly shared) term tree nodes.
  -- The former are usually initialized with dummy values so that it's cheap
  -- to check if any update has already been performed to a cell
  -- (allocating big vectors filled with zeros is too costly,
  -- especially if never used in an iteration, and adding to such vectors
  -- and especially using them as cotangent accumulators is wasteful.
  -- We take care to keep the scalar type of the dummy correct,
  -- but a shape is not preserved in a dummy, so it's not shape-correct.
  let s0 =
        let iMap =
              -- The first two cases are permitted for when the normal main
              -- parameters are used as parameters0.
              let f (DynamicRanked @r2 @n2 t) =
                    let sh = rshape @(Flip OR.Array) t
                    in Sh.withShapeP (shapeToList sh) $ \(Proxy @sh2) ->
                      DynamicRankedDummy @r2 @sh2 Proxy Proxy
                  f (DynamicShaped @r2 @sh2 _) =
                    DynamicShapedDummy @r2 @sh2 Proxy Proxy
                  f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
                  f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
              in EM.fromDistinctAscList
                 $ zip [toInputId 0 ..] $ map f $ V.toList parameters0
            dMap = EM.empty
            nMap = EM.empty
            astBindings = []
        in EvalState {..}
  in let -- Eval.
         EvalState{..} = buildFinMaps s0 deltaDt
         -- Extract results.
         !gradient = V.fromList $ EM.elems iMap
     in (astBindings, gradient)
-- The warnings in the following seems spurious. A GHC issue to be opened.
{- TODO: this causes a cyclic dependency:
{-# SPECIALIZE gradientFromDelta
  :: DomainsOD -> DeltaDt (Flip OR.Array) (Flip OS.Array) Double
  -> (AstBindingsD (Flip OR.Array), DomainsOD) #-}
{-# SPECIALIZE gradientFromDelta
  :: DomainsOD -> DeltaDt (AstRanked PrimalSpan) (AstShaped PrimalSpan) Double
  -> (AstBindingsD (AstRanked PrimalSpan), Domains (AstDynamic PrimalSpan)) #-}
-}

buildFinMaps
  :: forall ranked shaped r0.
     (GoodScalar r0, ADReady ranked, shaped ~ ShapedOf ranked)
  => EvalState ranked shaped -> DeltaDt ranked shaped r0
  -> EvalState ranked shaped
buildFinMaps s0 deltaDt =
  -- The first argument is the evaluation state being modified,
  -- the second is the cotangent accumulator that will become an actual
  -- cotangent contribution when complete (see below for an explanation)
  -- and the third argument is the node to evaluate.
  let evalRRuntimeSpecialized
        :: forall n r. (KnownNat n, GoodScalar r)
        => EvalState ranked shaped
        -> ranked r n -> DeltaR ranked r n
        -> EvalState ranked shaped
      evalRRuntimeSpecialized !s !c =
        -- We dispatch on all expected underyling scalar types, which is
        -- necessary to run the correct specialization when unpacking
        -- an existential type. All IfDifferentiable and RowSum instances should
        -- be included in the list of expected underlying scalar types.
        -- If the scalar type is not on the list, performance suffers greatly.
        -- TODO: can I pattern match on (typeRep @r) instead?
        case testEquality (typeRep @r) (typeRep @Double) of
          Just Refl -> evalR @n @Double s c
          _ -> case testEquality (typeRep @r) (typeRep @Float) of
            Just Refl -> evalR @n @Float s c
            _ -> case testEquality (typeRep @r) (typeRep @Int64) of
              Just Refl -> evalR @n @Int64 s c
              _ -> case testEquality (typeRep @r) (typeRep @CInt) of
                Just Refl -> evalR @n @CInt s c
                _ -> error "an unexpected underlying scalar type"
      evalRDynamicRanked
        :: EvalState ranked shaped
        -> (DynamicTensor ranked, DynamicTensor (DeltaR ranked))
        -> EvalState ranked shaped
      evalRDynamicRanked s3 ( DynamicRanked @rp @p t2
                            , DynamicRanked @rq @q d2 )
        | Just Refl <- sameNat (Proxy @q) (Proxy @p)
        , Just Refl <- testEquality (typeRep @rp) (typeRep @rq) =
            evalR s3 t2 d2
      evalRDynamicRanked _ _ =
        error "evalRDynamicRanked: unexpected constructor"
      evalSDynamicShaped
        :: EvalState ranked shaped
        -> (DynamicTensor ranked, DynamicTensor (DeltaR ranked))
        -> EvalState ranked shaped
      evalSDynamicShaped s3 ( DynamicShaped @rp @shp t2
                            , DynamicShaped @rq @shq d2 )
        | Just Refl <- sameShape @shq @shp
        , Just Refl <- testEquality (typeRep @rp) (typeRep @rq) =
            evalS s3 t2 d2
      evalSDynamicShaped _ _ =
        error "evalSDynamicShaped: unexpected constructor"
      evalR
        :: forall n r. (KnownNat n, GoodScalar r)
        => EvalState ranked shaped
        -> ranked r n -> DeltaR ranked r n
        -> EvalState ranked shaped
      evalR !s !c = let (abShared, cShared) = rregister c (astBindings s)
                        sShared = s {astBindings = abShared}
                    in \case
        ZeroR{} -> s
        InputR _ i -> s {iMap = EM.adjust (DynamicRanked . raddDynamic c) i
                                $ iMap s}
          -- This and similar don't need to be runtime-specialized,
          -- because the type of c determines the Num instance for (+).
        ScaleR k d -> evalR s (k * c) d
        AddR d e -> evalR (evalR sShared cShared d) cShared e
        LetR n d ->
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
                    ZeroR{} -> False
                    LetR{} -> False  -- wasteful and nonsensical
                    _ -> True)
          $ case EM.lookup n $ nMap s of
              Just (DeltaBindingR _) ->
                s {dMap = EM.adjust (DynamicRanked
                                     . raddDynamic c) n $ dMap s}
              Nothing ->
                let cs = DynamicRanked c
                in s { nMap = EM.insert n (DeltaBindingR d) $ nMap s
                     , dMap = EM.insert n cs $ dMap s }
              _ -> error "buildFinMaps: corrupted nMap"

        IndexR d ix -> evalR s (rscatter @ranked @r @0
                                             (shapeDelta d) c (const ix)) d
          -- equivalent: evalR s (updateNR (treplicate0NR sh 0) [(ix, c)]) d
        SumR d -> evalR s (rreplicate (lengthDelta d) c) d
        Sum0R d -> evalR s (rreplicate0N (shapeDelta d) c) d
        Dot0R v vd -> evalR s (v * rreplicate0N (rshape v) c) vd
                     -- too slow: evalR s (rmap0N (* (tscalar c)) v) vd
        ScatterR _sh d f -> evalR s (rgather (shapeDelta d) c f) d

        FromListR @n1 ld ->
          let cxs :: [ranked r n1]
              cxs = runravelToList cShared
          in foldl' (\ !s2 (cx, d2) -> evalR s2 cx d2) sShared
             $ zip cxs ld
        FromVectorR @n1 ld ->
          let cxs :: [ranked r n1]
              cxs = runravelToList cShared
          in foldl' (\ !s2 (cx, d2) -> evalR s2 cx d2) sShared
             $ zip cxs (V.toList ld)
        ReplicateR _n d -> evalR s (rsum c) d
        AppendR d e -> case rshape c of
          n :$ _ -> let k = lengthDelta d
                        s2 = evalR sShared (rslice 0 k cShared) d
                    in evalR s2 (rslice k (n - k) cShared) e
          ZS -> error "evalR: impossible pattern needlessly required"
        SliceR i n d -> case rshape c of
          n' :$ rest ->
            assert (n' == n `blame` (n', n)) $
            evalR s (rconcat [ rzero (i :$ rest)
                             , c
                             , rzero (lengthDelta d - i - n :$ rest) ])
                    d
          ZS -> error "evalR: impossible pattern needlessly required"
        ReverseR d -> evalR s (rreverse c) d
        TransposeR perm d ->
          let perm_reversed = map snd $ sort $ zip perm [0 .. length perm - 1]
          in evalR s (rtranspose perm_reversed c) d
        ReshapeR _sh d -> evalR s (rreshape (shapeDelta d) c) d
        GatherR _sh d f -> evalR s (rscatter (shapeDelta d) c f) d
        FoldR @rm @m p as _df rf x0' as' -> case rshape as of
          width :$ shm ->
            -- The call @rf cr x a@ is not shared here, but it's repeated
            -- just two times, so it's fine unless folds are nested badly,
            -- but then we have worse problems.
            let !_A1 = assert (rlength p == width + 1) ()
                shn = shapeDelta x0'
                domsToPair :: ADReady f => Domains f -> (f r n, f rm m)
                domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
                domsF = V.fromList [odFromSh @r shn, odFromSh @rm shm]
                crsr :: ranked r (1 + n)
                crsr =
                  rscanD (\cr doms' ->
                            rletDomainsIn domsF doms' $ \doms ->
                              let (x, a) = domsToPair doms
                              in rletDomainsIn
                                   domsF (rf cr x a) $ \rfRes ->
                                     fst $ domsToPair rfRes)
                         domsF
                         cShared  -- not duplicated directly, but just in case
                         (V.fromList
                            [ DynamicRanked $ rreverse $ rslice 0 width p
                            , DynamicRanked $ rreverse as ])
                crs = rreverse crsr
                -- We can't share crs via rlet, etc., because it appears
                -- in two different calls to evalR.
                (abShared2, crsShared) = rregister crs (astBindings sShared)
                sShared2 = sShared {astBindings = abShared2}
                rg :: ranked r (1 + n) -> ranked r (1 + n)
                   -> ranked rm (1 + m)
                   -> ranked rm (1 + m)
                rg = rzipWith31 (\cr x a ->
                                   rletDomainsIn domsF (rf cr x a) $ \rfRes ->
                                     snd $ domsToPair rfRes)
                cas = rg (rslice 1 width crsShared) (rslice 0 width p) as
                s2 = evalR sShared2 (crsShared ! (0 :. ZI)) x0'
            in evalR s2 cas as'
          ZS -> error "evalR: impossible pattern needlessly required"
        FoldRC @rm @m p as _df rf x0' as' ->
          -- No sharing attempted, because this constructor is usually used
          -- for non-symbolic derivatives.
          let las :: [ranked rm m]
              las = runravelToList as
              rg :: ranked r n
                 -> [(ranked r n, ranked rm m)]
                 -> (ranked r n, [ranked rm m])
              rg = mapAccumR rf
              (cx0, cas) = rg cShared (zip (init $ runravelToList p) las)
              s2 = evalR sShared cx0 x0'
          in evalR s2 (rfromList cas) as'
        FoldDR @rm @m domsOD p as _df rf x0' as' -> case V.unsnoc as of
          Nothing -> error "evalR: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "evalR: wrong rank of argument"
            0 : _ -> evalR s c x0'  -- TODO: needed?
            width : _shm ->
              let !_A1 = assert (rlength p == width + 1) ()
                  shn = shapeDelta x0'
                  domsF = V.cons (odFromSh @r shn) domsOD
                  domsToPair :: forall f. ADReady f
                             => Domains f -> (f r n, Domains f)
                  domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
                  lp = rreverse p
                  las :: Domains ranked
                  las = mapDomainsRanked11 rreverse as
                  crsr :: ranked r (1 + n)
                  crsr =
                    rscanD (\cr doms' ->
                      rletDomainsIn domsF doms' $ \doms ->
                        let (x, a) = domsToPair doms
                        in rletDomainsIn
                             domsF (rf cr x (dmkDomains a)) $ \rfRes ->
                               fst $ domsToPair rfRes)
                           domsF
                           cShared  -- not duplicated directly, but just in case
                           (V.cons (DynamicRanked lp) las)
                  crs = rreverse crsr
                  (abShared2, crsShared) = rregister crs (astBindings sShared)
                  sShared2 = sShared {astBindings = abShared2}
                  rg :: [ranked r n] -> [ranked r n]
                     -> [DomainsOf ranked]  -- [m]
                     -> [Domains ranked]  -- [m]
                  rg = zipWith3 (\cr x a ->
                                   snd $ domsToPair $ dunDomains domsF
                                   $ rf cr x a)
                  cas = ravelDomains
                        $ rg (runravelToList $ rslice 1 width crsShared)
                             (runravelToList $ rslice 0 width p)
                             (map dmkDomains $ unravelDomains as)
                  s2 = evalR sShared2 (crsShared ! (0 :. ZI)) x0'
              in V.foldl' evalRDynamicRanked s2 $ V.zip cas as'
        FoldDRC @rm @m domsOD p as _df rf x0' as' ->
          -- No sharing attempted, because this constructor is usually used
          -- for non-symbolic derivatives.
          let shn = shapeDelta x0'
              domsF = V.cons (odFromSh @r shn) domsOD
              domsToPair :: forall f. ADReady f
                         => Domains f -> (f r n, Domains f)
              domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
              rg :: ranked r n
                 -> [(ranked r n, DomainsOf ranked)]
                 -> (ranked r n, [Domains ranked])
              rg = mapAccumR (\cx (x, a) ->
                                domsToPair $ dunDomains domsF $ rf cx x a)
              (cx0, cas) = rg cShared
                              (zip (init $ runravelToList p)
                                   (map dmkDomains $ unravelDomains as))
              s2 = evalR sShared cx0 x0'
          in V.foldl' evalRDynamicRanked s2 $ V.zip (ravelDomains cas) as'
        ScanR @rm @m @_ @_ @n1 p as _df rf x0' as' -> case rshape as of
          0 :$ _ -> evalR s (c ! (0 :. ZI)) x0'
          width :$ shm ->
            let !_A1 = assert (rlength p == width + 1) ()
                !_A2 = assert (rlength cShared == width + 1) ()
                shn = shapeDelta x0'
                domsToPair :: ADReady f => Domains f -> (f r n1, f rm m)
                domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
                domsF = V.fromList [odFromSh @r shn, odFromSh @rm shm]
                -- The domain must be @Int@ due to rslice and so can't be
                -- @IndexOf ranked 0@ for rbuild nor @ranked Int 0@ for rmap.
                -- We can't fold nor scan over g1/g2, because it's not closed.
                -- We can't multiply by a unitriangular matrix instead of
                -- using slice, because rf can have a constant component
                -- and then it gets summed over the zero area of the matrix.
                g1 :: Int -> ranked r (1 + n1)
                g1 k =
                  let cx = cShared ! (fromIntegral k :. ZI)
                      rf1 =
                        rscanD (\cr doms' ->
                                  rletDomainsIn domsF doms' $ \doms ->
                                    let (x, a) = domsToPair doms
                                    in rletDomainsIn
                                         domsF (rf cr x a) $ \rfRes ->
                                           fst $ domsToPair rfRes)
                               domsF
                               cx
                               (V.fromList
                                  [ DynamicRanked $ rreverse $ rslice 0 k p
                                  , DynamicRanked $ rreverse $ rslice 0 k as ])
                      padding = rzero (width - k :$ shn)
                  in rappend (rreverse rf1) padding
                g1s = map g1 [1 .. width]  -- can't be rmap nor rbuild nor rscan
                g1t = rfromList g1s
                (abShared2, g1tShared) = rregister g1t (astBindings sShared)
                sShared2 = sShared {astBindings = abShared2}
                g1sum = cShared ! (0 :. ZI) + rsum (rtr g1tShared ! (0 :. ZI))
                g2 :: Int -> ranked rm (1 + m)
                g2 k =
                  let rf11 = rslice 1 k $ g1tShared ! (fromIntegral k - 1 :. ZI)
                      lp = rslice 0 k p
                      las = rslice 0 k as
                      rg :: ranked r (1 + n1) -> ranked r (1 + n1)
                         -> ranked rm (1 + m)
                         -> ranked rm (1 + m)
                      rg = rzipWith31 (\cr x a ->
                             rletDomainsIn domsF (rf cr x a) $ \rfRes ->
                                snd $ domsToPair rfRes)
                      cas = rg rf11 lp las
                      padding = rzero (width - k :$ shm)
                  in rappend cas padding
                g2s = map g2 [1..width]  -- can't be rmap nor rbuild nor rscan
                g2sum = rsum $ rfromList g2s
                s2 = evalR sShared2 g1sum x0'
            in evalR s2 g2sum as'
          ZS -> error "evalR: impossible pattern needlessly required"
        ScanDR @_ @_ @n1 domsOD p as _df rf x0' as' -> case V.unsnoc as of
          Nothing -> error "evalR: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "evalR: wrong rank of argument"
            0 : _ -> evalR s (c ! (0 :. ZI)) x0'
            width : _ ->
              let !_A1 = assert (rlength p == width + 1) ()
                  !_A2 = assert (rlength cShared == width + 1) ()
                  shn = shapeDelta x0'
                  domsF = V.cons (odFromSh @r shn) domsOD
                  domsToPair :: forall f. ADReady f
                             => Domains f -> (f r n1, Domains f)
                  domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
                  g1 :: Int -> ranked r (1 + n1)
                  g1 k =
                    let cx = cShared ! (fromIntegral k :. ZI)
                        lp = rreverse $ rslice 0 k p
                        las :: Domains ranked
                        las = mapDomainsRanked11 (rreverse . rslice 0 k) as
                        rf1 =
                          rscanD (\cr doms' ->
                                    rletDomainsIn domsF doms' $ \doms ->
                                      let (x, a) = domsToPair doms
                                      in rletDomainsIn
                                           domsF
                                           (rf cr x (dmkDomains a)) $ \rfRes ->
                                             fst $ domsToPair rfRes)
                                 domsF cx
                                 (V.cons (DynamicRanked lp) las)
                        padding = rzero (width - k :$ shn)
                    in rappend (rreverse rf1) padding
                  g1s = map g1 [1 .. width]  -- can't be rmap, rbuild nor rscan
                  g1t = rfromList g1s
                  (abShared2, g1tShared) = rregister g1t (astBindings sShared)
                  sShared2 = sShared {astBindings = abShared2}
                  g1sum = cShared ! (0 :. ZI) + rsum (rtr g1tShared ! (0 :. ZI))
                  g2 :: Int -> Domains ranked  -- 1 + m
                  g2 k =
                    let rf11 = rslice 1 k
                               $ g1tShared ! (fromIntegral k - 1 :. ZI)
                        lp = rslice 0 k p
                        las :: Domains ranked  -- 1 + m
                        las = mapDomainsRanked11 (rslice 0 k) as
                        -- TODO: use rzipWith31 (rzipWithDomains31?)
                        rg :: [ranked r n1] -> [ranked r n1]
                           -> [DomainsOf ranked]  -- [m]
                           -> [Domains ranked]  -- [m]
                        rg = zipWith3 (\cr x a ->
                                         snd $ domsToPair $ dunDomains domsF
                                         $ rf cr x a)
                        cas = rg (runravelToList rf11)
                                 (runravelToList lp)
                                 (map dmkDomains $ unravelDomains las)
                        padRanked :: DynamicTensor ranked
                                  -> DynamicTensor ranked
                        padRanked (DynamicRanked t) = case rshape t of
                          ZS -> error "padRanked: wrong shape"
                          kk :$ shm -> assert (kk == k) $
                            let padding = rzero (width - k :$ shm)
                            in DynamicRanked $ rappend t padding
                        padRanked _ = error "padRanked: not DynamicRanked"
                    in V.map padRanked (ravelDomains cas)
                  g2s = map g2 [1..width]  -- can't be rmap nor rbuild nor rscan
                  g2sum = V.fromList $ map sumDynamicRanked
                          $ transpose $ map V.toList g2s
                  s2 = evalR sShared2 g1sum x0'
              in V.foldl' evalRDynamicRanked s2 $ V.zip g2sum as'
        CastR d -> evalRRuntimeSpecialized s (rcast c) d

        SToR (RToS d) -> evalR s c d  -- no information lost, so no checks
        SToR d -> evalS s (sfromR c) d

      evalSRuntimeSpecialized
        :: forall sh r. (Sh.Shape sh, GoodScalar r)
        => EvalState ranked shaped
        -> shaped r sh -> DeltaS shaped r sh
        -> EvalState ranked shaped
      evalSRuntimeSpecialized !s !c =
        case testEquality (typeRep @r) (typeRep @Double) of
          Just Refl -> evalS @sh @Double s c
          _ -> case testEquality (typeRep @r) (typeRep @Float) of
            Just Refl -> evalS @sh @Float s c
            _ -> case testEquality (typeRep @r) (typeRep @Int64) of
              Just Refl -> evalS @sh @Int64 s c
              _ -> case testEquality (typeRep @r) (typeRep @CInt) of
                Just Refl -> evalS @sh @CInt s c
                _ -> error "an unexpected underlying scalar type"
      evalS
        :: forall sh r. (Sh.Shape sh, GoodScalar r)
        => EvalState ranked shaped
        -> shaped r sh -> DeltaS shaped r sh
        -> EvalState ranked shaped
      evalS !s !c = let (abShared, cShared) = sregister c (astBindings s)
                        sShared = s {astBindings = abShared}
                    in \case
        ZeroS -> s
        InputS i -> s {iMap = EM.adjust (DynamicShaped . saddDynamic c) i
                              $ iMap s}
        ScaleS k d -> evalS s (k * c) d
        AddS d e -> evalS (evalS sShared cShared d) cShared e
        LetS n d ->
          assert (case d of
                    ZeroS -> False
                    LetS{} -> False  -- wasteful and nonsensical
                    _ -> True)
          $ case EM.lookup n $ nMap s of
              Just (DeltaBindingS _) ->
                s {dMap = EM.adjust (DynamicShaped . saddDynamic c) n $ dMap s}
              Nothing ->
                let cs = DynamicShaped c
                in s { nMap = EM.insert n (DeltaBindingS d) $ nMap s
                     , dMap = EM.insert n cs $ dMap s }
              _ -> error "buildFinMaps: corrupted nMap"

        IndexS @sh1 d ix ->
          gcastWith (unsafeCoerce Refl
                     :: Sh.Drop (Sh.Rank sh1) (sh1 Sh.++ sh) :~: sh)
          $ gcastWith (unsafeCoerce Refl
                       :: Sh.Take (Sh.Rank sh1) (sh1 Sh.++ sh) :~: sh1)
          $ evalS s (sscatter @shaped @r @'[] @(Sh.Rank sh1) c (const ix)) d
          -- equivalent: evalS s (updateNR (replicate0NR sh 0) [(ix, c)]) d
        SumS d -> evalS s (sreplicate c) d
        Sum0S d -> evalS s (sreplicate0N c) d
        Dot0S v vd -> evalS s (v * sreplicate0N c) vd
          -- too slow: evalS s (smap0N (* (sscalar c)) v) vd
        ScatterS d f -> evalS s (sgather c f) d

        FromListS ld ->
          ifoldl' (\ !s2 i d2 ->
            evalS s2 (cShared !$ (fromIntegral i :$: ZSH)) d2) sShared ld
        FromVectorS ld ->
          V.ifoldl' (\ !s2 i d2 ->
            evalS s2 (cShared !$ (fromIntegral i :$: ZSH)) d2) sShared ld
        ReplicateS d -> evalS s (ssum c) d
        AppendS @_ @_ @m d e ->
          let s2 = evalS sShared (sslice (Proxy @0) Proxy cShared) d
          in evalS s2 (sslice (Proxy @m) Proxy cShared) e
        SliceS @_ @i d ->
          evalS s (sappend @shaped @r @i 0 (sappend c 0)) d
        ReverseS d -> evalS s (sreverse c) d
        TransposeS @_ @perm @_ @sh2 d ->
          -- Reversing the permutation at the type level would be too hard,
          -- so we unsafeCoerce, knowing that it's safe in this case.
          -- TODO: instead add a tensor operation that permutes
          -- in the other direction? What if the backend doesn't have it?
          let perm = Sh.shapeT @perm
              permRev = map snd $ sort $ zip perm [0 .. length perm - 1]
          in Sh.withShapeP permRev $ \(Proxy @permR) ->
            gcastWith (unsafeCoerce Refl
                       :: Sh.Permute permR sh :~: sh2)
            $ gcastWith (unsafeCoerce Refl
                         :: Sh.Rank sh :~: Sh.Rank sh2)
            $ gcastWith (unsafeCoerce Refl
                         :: Sh.Rank permR :~: Sh.Rank perm)
            $ evalS s
                    (trustMeThisIsAPermutation @permR
                       (stranspose (Proxy @permR))
                       c)
                    d
        ReshapeS d -> evalS s (sreshape c) d
        GatherS d f -> evalS s (sscatter c f) d
        FoldS @rm @shm @k p as _df rf x0' as' ->
          let domsToPair :: ADReadyS f
                         => Domains (RankedOf f) -> (f r sh, f rm shm)
              domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
              domsF = V.fromList [odFromShS @r @sh, odFromShS @rm @shm]
              crsr :: shaped r (1 + k ': sh)
              crsr =
                sscanD (\cr doms' ->
                          sletDomainsIn domsF doms' $ \doms ->
                            let (x, a) = domsToPair doms
                            in sletDomainsIn
                                 domsF (rf cr x a) $ \rfRes ->
                                   fst $ domsToPair rfRes)
                       domsF
                       cShared  -- not duplicated directly, but just in case
                       (V.fromList
                          [ DynamicShaped $ sreverse
                            $ sslice @_ @_ @_ @_ @1
                                     (Proxy @0) (Proxy @k) p
                          , DynamicShaped $ sreverse as ])
              crs = sreverse crsr
              (abShared2, crsShared) = sregister crs (astBindings sShared)
              sShared2 = sShared {astBindings = abShared2}
              rg :: shaped r (k ': sh) -> shaped r (k ': sh)
                 -> shaped rm (k ': shm)
                 -> shaped rm (k ': shm)
              rg = szipWith31 (\cr x a ->
                                 sletDomainsIn domsF (rf cr x a) $ \rfRes ->
                                   snd $ domsToPair rfRes)
              cas = rg (sslice @_ @_ @_ @_ @0
                               (Proxy @1) (Proxy @k) crsShared)
                       (sslice @_ @_ @_ @_ @1
                               (Proxy @0) (Proxy @k) p) as
              s2 = evalS sShared2 (crsShared !$ (0 :$: ZSH)) x0'
          in evalS s2 cas as'
        FoldSC @rm @shm p as _df rf x0' as' ->
          -- No sharing attempted, because this constructor is usually used
          -- for shon-symbolic derivatives.
          let las :: [shaped rm shm]
              las = sunravelToList as
              rg :: shaped r sh
                 -> [(shaped r sh, shaped rm shm)]
                 -> (shaped r sh, [shaped rm shm])
              rg = mapAccumR rf
              (cx0, cas) = rg cShared (zip (init $ sunravelToList p) las)
              s2 = evalS sShared cx0 x0'
          in evalS s2 (sfromList cas) as'
{-
        FoldDS @rm @m domsOD p as _df rf x0' as' -> case V.unsnoc as of
          Nothing -> error "evalR: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "evalR: wrong rank of argument"
            0 : _ -> evalR s c x0'  -- TODO: needed?
            width : _shm ->
              let !_A1 = assert (rlength p == width + 1) ()
                  shn = shapeDelta x0'
                  domsF = V.cons (odFromSh @r shn) domsOD
                  domsToPair :: forall f. ADReady f
                             => Domains f -> (f r sh, Domains f)
                  domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
                  lp = rreverse p
                  las :: Domains shaped
                  las = mapDomainsRanked11 rreverse as
                  crsr :: shaped r (1 + n)
                  crsr =
                    rscanD (\cr doms' ->
                      rletDomainsIn domsF doms' $ \doms ->
                        let (x, a) = domsToPair doms
                        in rletDomainsIn
                             domsF (rf cr x (dmkDomains a)) $ \rfRes ->
                               fst $ domsToPair rfRes)
                           domsF
                           cShared  -- not duplicated directly, but just in case
                           (V.cons (DynamicRanked lp) las)
                  crs = rreverse crsr
                  (abShared2, crsShared) = rregister crs (astBindings sShared)
                  sShared2 = sShared {astBindings = abShared2}
                  rg :: [shaped r sh] -> [shaped r sh]
                     -> [DomainsOf shaped]  -- [m]
                     -> [Domains shaped]  -- [m]
                  rg = zipWith3 (\cr x a ->
                                   snd $ domsToPair $ dunDomains domsF
                                   $ rf cr x a)
                  cas = ravelDomains
                        $ rg (runravelToList $ rslice 1 width crsShared)
                             (runravelToList $ rslice 0 width p)
                             (map dmkDomains $ unravelDomains as)
                  s2 = evalR sShared2 (crsShared ! (0 :. ZI)) x0'
              in V.foldl' evalRDynamicRanked s2 $ V.zip cas as'
-}
        FoldDSC @rm @shm domsOD p as _df rf x0' as' ->
          -- No sharing attempted, because this constructor is usually used
          -- for shon-symbolic derivatives.
          let domsF = V.cons (odFromShS @r @sh) domsOD
              domsToPair :: forall f. ADReadyS f
                         => Domains (RankedOf f)
                         -> (f r sh, Domains (RankedOf f))
              domsToPair doms = (sfromD $ doms V.! 0, V.tail doms)
              rg :: shaped r sh
                 -> [(shaped r sh, DomainsOf (RankedOf shaped))]
                 -> (shaped r sh, [Domains (RankedOf shaped)])
              rg = mapAccumR (\cx (x, a) ->
                                domsToPair $ dunDomains domsF $ rf cx x a)
              (cx0, cas) = rg cShared
                              (zip (init $ sunravelToList p)
                                   (map dmkDomains $ unravelDomains as))
              s2 = evalS sShared cx0 x0'
          in V.foldl' evalSDynamicShaped s2 $ V.zip (ravelDomains cas) as'
{-
        ScanS @rm @m @_ @_ @n1 p as _df rf x0' as' -> case rshape as of
          0 :$ _ -> evalR s (c ! (0 :. ZI)) x0'
          width :$ shm ->
            let !_A1 = assert (rlength p == width + 1) ()
                !_A2 = assert (rlength cShared == width + 1) ()
                shn = shapeDelta x0'
                domsToPair :: ADReady f => Domains f -> (f r sh1, f rm shm)
                domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
                domsF = V.fromList [odFromSh @r shn, odFromSh @rm shm]
                -- The domain must be @Int@ due to rslice and so can't be
                -- @IndexOf shaped 0@ for rbuild nor @shaped Int 0@ for rmap.
                -- We can't fold nor scan over g1/g2, because it's not closed.
                -- We can't multiply by a unitriangular matrix instead of
                -- using slice, because rf can have a constant component
                -- and then it gets summed over the zero area of the matrix.
                g1 :: Int -> shaped r (1 + n1)
                g1 k =
                  let cx = cShared ! (fromIntegral k :. ZI)
                      rf1 =
                        rscanD (\cr doms' ->
                                  rletDomainsIn domsF doms' $ \doms ->
                                    let (x, a) = domsToPair doms
                                    in rletDomainsIn
                                         domsF (rf cr x a) $ \rfRes ->
                                           fst $ domsToPair rfRes)
                               domsF
                               cx
                               (V.fromList
                                  [ DynamicRanked $ rreverse $ rslice 0 k p
                                  , DynamicRanked $ rreverse $ rslice 0 k as ])
                      padding = rzero (width - k :$ shn)
                  in rappend (rreverse rf1) padding
                g1s = map g1 [1 .. width]  -- can't be rmap nor rbuild nor rscan
                g1t = rfromList g1s
                (abShared2, g1tShared) = rregister g1t (astBindings sShared)
                sShared2 = sShared {astBindings = abShared2}
                g1sum = cShared ! (0 :. ZI) + rsum (rtr g1tShared ! (0 :. ZI))
                g2 :: Int -> shaped rm (1 + m)
                g2 k =
                  let rf11 = rslice 1 k $ g1tShared ! (fromIntegral k - 1 :. ZI)
                      lp = rslice 0 k p
                      las = rslice 0 k as
                      rg :: shaped r (1 + n1) -> shaped r (1 + n1)
                         -> shaped rm (1 + m)
                         -> shaped rm (1 + m)
                      rg = rzipWith31 (\cr x a ->
                             rletDomainsIn domsF (rf cr x a) $ \rfRes ->
                                snd $ domsToPair rfRes)
                      cas = rg rf11 lp las
                      padding = rzero (width - k :$ shm)
                  in rappend cas padding
                g2s = map g2 [1..width]  -- can't be rmap nor rbuild nor rscan
                g2sum = rsum $ rfromList g2s
                s2 = evalR sShared2 g1sum x0'
            in evalR s2 g2sum as'
          ZS -> error "evalR: impossible pattern needlessly required"
        ScanDS @_ @_ @n1 domsOD p as _df rf x0' as' -> case V.unsnoc as of
          Nothing -> error "evalR: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "evalR: wrong rank of argument"
            0 : _ -> evalR s (c ! (0 :. ZI)) x0'
            width : _ ->
              let !_A1 = assert (rlength p == width + 1) ()
                  !_A2 = assert (rlength cShared == width + 1) ()
                  shn = shapeDelta x0'
                  domsF = V.cons (odFromSh @r shn) domsOD
                  domsToPair :: forall f. ADReady f
                             => Domains f -> (f r sh1, Domains f)
                  domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
                  g1 :: Int -> shaped r (1 + n1)
                  g1 k =
                    let cx = cShared ! (fromIntegral k :. ZI)
                        lp = rreverse $ rslice 0 k p
                        las :: Domains shaped
                        las = mapDomainsRanked11 (rreverse . rslice 0 k) as
                        rf1 =
                          rscanD (\cr doms' ->
                                    rletDomainsIn domsF doms' $ \doms ->
                                      let (x, a) = domsToPair doms
                                      in rletDomainsIn
                                           domsF
                                           (rf cr x (dmkDomains a)) $ \rfRes ->
                                             fst $ domsToPair rfRes)
                                 domsF cx
                                 (V.cons (DynamicRanked lp) las)
                        padding = rzero (width - k :$ shn)
                    in rappend (rreverse rf1) padding
                  g1s = map g1 [1 .. width]  -- can't be rmap, rbuild nor rscan
                  g1t = rfromList g1s
                  (abShared2, g1tShared) = rregister g1t (astBindings sShared)
                  sShared2 = sShared {astBindings = abShared2}
                  g1sum = cShared ! (0 :. ZI) + rsum (rtr g1tShared ! (0 :. ZI))
                  g2 :: Int -> Domains shaped  -- 1 + m
                  g2 k =
                    let rf11 = rslice 1 k
                               $ g1tShared ! (fromIntegral k - 1 :. ZI)
                        lp = rslice 0 k p
                        las :: Domains shaped  -- 1 + m
                        las = mapDomainsRanked11 (rslice 0 k) as
                        -- TODO: use rzipWith31 (rzipWithDomains31?)
                        rg :: [shaped r sh1] -> [shaped r sh1]
                           -> [DomainsOf shaped]  -- [m]
                           -> [Domains shaped]  -- [m]
                        rg = zipWith3 (\cr x a ->
                                         snd $ domsToPair $ dunDomains domsF
                                         $ rf cr x a)
                        cas = rg (runravelToList rf11)
                                 (runravelToList lp)
                                 (map dmkDomains $ unravelDomains las)
                        padRanked :: DynamicTensor shaped
                                  -> DynamicTensor shaped
                        padRanked (DynamicRanked t) = case rshape t of
                          ZS -> error "padRanked: wrong shape"
                          kk :$ shm -> assert (kk == k) $
                            let padding = rzero (width - k :$ shm)
                            in DynamicRanked $ rappend t padding
                        padRanked _ = error "padRanked: not DynamicRanked"
                    in V.map padRanked (ravelDomains cas)
                  g2s = map g2 [1..width]  -- can't be rmap nor rbuild nor rscan
                  g2sum = V.fromList $ map sumDynamicRanked
                          $ transpose $ map V.toList g2s
                  s2 = evalR sShared2 g1sum x0'
              in V.foldl' evalRDynamicRanked s2 $ V.zip g2sum as'
-}
        CastS d -> evalSRuntimeSpecialized s (scast c) d
        RToS (SToR @sh2 d) ->
          case sameShape @sh @sh2 of
            Just Refl -> evalS s c d
            _ -> error "buildFinMaps: different shapes in RToS(SToR)"
        RToS d -> evalR s (rfromS c) d

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
          in s {iMap = EM.adjust f i $ iMap s}
        Index0 (LetR n d) ixs' sh ->
          let ixs = indexToList ixs'
          in case EM.lookup n $ nMap s of
            Just (DeltaBindingR _) ->
              let f v = v `OD.update` [(ixs, v `rindex0D` ixs + c)]
              in s {dMap = EM.adjust f n $ dMap s}
                -- This would be an asymptotic optimization compared to
                -- the general case below, if not for the non-mutable update,
                -- which implies copying the whole @v@ vector,
                -- so it's only several times faster (same allocation,
                -- but not adding to each cell of @v@).
            Nothing ->
              let v = treplicate0ND sh 0 `OD.update` [(ixs, c)]
              in s { nMap = EM.insert n (DeltaBindingR d) $ nMap s
                   , dMap = EM.insert n v $ dMap s }
            _ -> error "buildFinMaps: corrupted nMap"
-}

      evalFromnMap :: EvalState ranked shaped -> EvalState ranked shaped
      evalFromnMap s@EvalState{nMap, dMap} =
        case EM.maxViewWithKey nMap of
          Just ((n, b), nMap2) ->
            let s2 = s {nMap = nMap2}
                s3 = case b of
                  DeltaBindingR @n1 @r1 d -> case dMap EM.! n of
                    DynamicRanked @r2 @n2 c -> case sameNat (Proxy @n2)
                                                            (Proxy @n1) of
                      Just Refl -> case testEquality (typeRep @r1)
                                                     (typeRep @r2) of
                        Just Refl -> evalRRuntimeSpecialized s2 c d
                        _ -> error "buildFinMaps: scalar mismatch"
                      _ -> error "buildFinMaps: rank mismatch"
                    DynamicShaped{} ->
                      error "evalFromnMap: DynamicShaped"
                    DynamicRankedDummy{} ->
                      error "evalFromnMap: DynamicRankedDummy"
                    DynamicShapedDummy{} ->
                      error "evalFromnMap: DynamicShapedDummy"
                  DeltaBindingS @sh1 @r1 d -> case dMap EM.! n of
                    DynamicRanked{} ->
                      error "evalFromnMap: DynamicRanked"
                    DynamicShaped @r2 @sh2 c -> case sameShape @sh2 @sh1 of
                      Just Refl -> case testEquality (typeRep @r1)
                                                     (typeRep @r2) of
                        Just Refl -> evalSRuntimeSpecialized s2 c d
                        _ -> error "buildFinMaps: scalar mismatch"
                      _ -> error "buildFinMaps: shape mismatch"
                    DynamicRankedDummy{} ->
                      error "evalFromnMap: DynamicRankedDummy"
                    DynamicShapedDummy{} ->
                      error "evalFromnMap: DynamicShapedDummy"
            in evalFromnMap s3
          Nothing -> s  -- loop ends

      s1 = case deltaDt of
        DeltaDtR dt deltaTopLevel -> evalR s0 dt deltaTopLevel
        DeltaDtS dt deltaTopLevel -> evalS s0 dt deltaTopLevel
  in evalFromnMap s1
{- TODO: this causes a cyclic dependency:
{-# SPECIALIZE buildFinMaps
  :: EvalState (Flip OR.Array) (Flip OS.Array) -> DeltaDt (Flip OR.Array) (Flip OS.Array) Double -> EvalState (Flip OR.Array) (Flip OS.Array) #-}
{-# SPECIALIZE buildFinMaps
  :: EvalState (AstRanked PrimalSpan) (AstShaped PrimalSpan) -> DeltaDt (AstRanked PrimalSpan) (AstShaped PrimalSpan) Double -> EvalState (AstRanked PrimalSpan) (AstShaped PrimalSpan) #-}
-}

mapDomainsDeltaR11
  :: (RankedTensor ranked, ShapedTensor (ShapedOf ranked))
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => DeltaR ranked rq (1 + q) -> DeltaR ranked rq (1 + q))
  -> Domains (DeltaR ranked) -> Domains (DeltaR ranked)
mapDomainsDeltaR11 f = V.map (mapDeltaR11 f)

mapDeltaR11
  :: (RankedTensor ranked, ShapedTensor (ShapedOf ranked))
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => DeltaR ranked rq (1 + q) -> DeltaR ranked rq (1 + q))
  -> DynamicTensor (DeltaR ranked) -> DynamicTensor (DeltaR ranked)
mapDeltaR11 f (DynamicRanked t) = case shapeDelta t of
  ZS -> error "mapDeltaR11: rank 0"
  _ :$ _ -> DynamicRanked $ f t
mapDeltaR11 _ _ = error "mapDeltaR11: not DynamicRanked"

mapDomainsDeltaS11kk
  :: forall k k1 shaped.
     (ShapedOf (RankedOf shaped) ~ shaped, KnownNat k, KnownNat k1)
  => (forall rq shq. (GoodScalar rq, Sh.Shape shq)
      => DeltaS shaped rq (k ': shq) -> DeltaS shaped rq (k1 ': shq))
  -> Domains (DeltaR (RankedOf shaped)) -> Domains (DeltaR (RankedOf shaped))
mapDomainsDeltaS11kk f = V.map (mapDeltaS11kk f)

mapDeltaS11kk
  :: forall k k1 shaped.
     (ShapedOf (RankedOf shaped) ~ shaped, KnownNat k, KnownNat k1)
  => (forall rq shq. (GoodScalar rq, Sh.Shape shq)
      => DeltaS shaped rq (k ': shq) -> DeltaS shaped rq (k1 ': shq))
  -> DynamicTensor (DeltaR (RankedOf shaped))
  -> DynamicTensor (DeltaR (RankedOf shaped))
mapDeltaS11kk f (DynamicShaped @_ @sh t) = case ShapedList.shapeSh @sh of
  ZSH -> error "mapDeltaS11kk: rank 0"
  (:$:) @n _ _ -> case sameNat (Proxy @n) (Proxy @k) of
    Just Refl -> DynamicShaped $ f t
    Nothing -> error "mapDeltaS11kk: wrong width"
mapDeltaS11kk _ _ = error "mapDeltaS11kk: not DynamicRanked"


-- * Forward derivative computation from the delta expressions

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
--
-- This mimics 'buildFinMaps', but in reverse. Perhaps this can be
-- simplified, but the obvious simplest formulation does not honour sharing
-- and evaluates shared subexpressions repeatedly.
buildDerivative
  :: forall ranked shaped r0 s.
     (GoodScalar r0, ADReady ranked, shaped ~ ShapedOf ranked)
  => Int -> DeltaDt ranked shaped r0 -> Domains ranked
  -> ST s (AstBindingsD ranked, DeltaDt ranked shaped r0)
buildDerivative dimR deltaDt params = do
  dMap <- newSTRef EM.empty
  nMap <- newSTRef EM.empty
  astBindings <- newSTRef []
  let evalRDynamicRanked
        :: DynamicTensor (DeltaR ranked) -> ST s (DynamicTensor ranked)
      evalRDynamicRanked (DynamicRanked @rq @q d) = do
        t <- evalR d
        return $! DynamicRanked t
      evalRDynamicRanked _ =
        error "evalRDynamicRanked: unexpected constructor"
      evalSDynamicShaped
        :: DynamicTensor (DeltaR ranked) -> ST s (DynamicTensor ranked)
      evalSDynamicShaped (DynamicShaped @rq @shq d) = do
        t <- evalS d
        return $! DynamicShaped t
      evalSDynamicShaped _ =
        error "evalSDynamicShaped: unexpected constructor"
      evalR
        :: forall n r. (KnownNat n, GoodScalar r)
        => DeltaR ranked r n -> ST s (ranked r n)
      evalR = \case
        ZeroR sh -> return $ rzero sh
        InputR _ (InputId i) ->
          if i < dimR
          then case params V.! i of
            DynamicRanked @r2 @n2 e -> case sameNat (Proxy @n2) (Proxy @n) of
              Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
                Just Refl -> return e
                _ -> error "buildDerivative: scalar mismatch"
              _ -> error "buildDerivative: rank mismatch"
            DynamicShaped{} -> error "buildDerivative: DynamicShaped"
            DynamicRankedDummy{} -> error "buildDerivative: DynamicRankedDummy"
            DynamicShapedDummy{} -> error "buildDerivative: DynamicShapedDummy"
          else error "buildDerivative': wrong index for an input"
        ScaleR k d -> (* k) <$> evalR d
        AddR d e -> liftM2 (+) (evalR d) (evalR e)
        LetR n d -> do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBindingR _) -> do
              dm <- readSTRef dMap
              case dm EM.! n of
                DynamicRanked @r2 @n2 e -> case sameNat (Proxy @n2)
                                                        (Proxy @n) of
                  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
                    Just Refl -> return e
                    _ -> error "buildDerivative: scalar mismatch"
                  _ -> error "buildDerivative: rank mismatch"
                DynamicShaped{} -> error "buildDerivative: DynamicShaped"
                DynamicRankedDummy{} ->
                  error "buildDerivative: DynamicRankedDummy"
                DynamicShapedDummy{} ->
                  error "buildDerivative: DynamicShapedDummy"
            Nothing -> do
              cRaw <- evalR d
              ab <- readSTRef astBindings
              let (abShared, cShared) = rregister cRaw ab
              writeSTRef astBindings abShared
              nmNew <- readSTRef nMap
              writeSTRef nMap $! EM.insert n (DeltaBindingR d) nmNew
              dm <- readSTRef dMap
              writeSTRef dMap $! EM.insert n (DynamicRanked cShared) dm
              return cShared
            _ -> error "buildDerivative: corrupted nMap"

        IndexR d ix -> (`rindex` ix) <$> evalR d
        SumR d -> rsum <$> evalR d
        Sum0R ZeroR{} -> return 0
        Sum0R d -> rsum0 <$> evalR d
        Dot0R _ ZeroR{} -> return 0
        Dot0R v d -> rdot0 v <$> evalR d
        ScatterR sh d f -> do
          t <- evalR d
          return $! rscatter sh t f

        FromListR lsd -> do
          l <- mapM evalR lsd
          return $! rfromList l
        FromVectorR lsd -> do
          l <- V.mapM evalR lsd
          return $! rfromVector l
        ReplicateR n d -> do
          t <- evalR d
          return $! rreplicate n t
        AppendR d e -> liftM2 rappend (evalR d) (evalR e)
        SliceR i n d -> rslice i n <$> evalR d
        ReverseR d -> rreverse <$> evalR d
        TransposeR perm d -> rtranspose perm <$> evalR d
        ReshapeR sh d -> rreshape sh <$> evalR d
        GatherR sh d f -> do
          t <- evalR d
          return $! rgather sh t f
        FoldR @rm @m p as df _rf x0' as' -> case rshape as of
          width :$ shm -> do
            let !_A1 = assert (rlength p == width + 1) ()
                shn = shapeDelta x0'
            cx0 <- evalR x0'
            cas <- evalR as'
            let domsTo3 :: ADReady f => Domains f -> (f rm m, f r n, f rm m)
                domsTo3 doms = ( rfromD $ doms V.! 0
                               , rfromD $ doms V.! 1
                               , rfromD $ doms V.! 2 )
                domsF =
                  V.fromList
                    [odFromSh @rm shm, odFromSh @r shn, odFromSh @rm shm]
            return $! rfoldD (\cx doms' ->
                                rletDomainsIn domsF doms' $ \doms ->
                                  let (ca, x, a) = domsTo3 doms
                                  in df cx ca x a)
                             domsF
                             cx0
                             (V.fromList
                                [ DynamicRanked cas
                                , DynamicRanked $ rslice 0 width p
                                , DynamicRanked as ])
          ZS -> error "evalR: impossible pattern needlessly required"
        FoldRC p as df _rf x0' as' -> do
          cx0 <- evalR x0'
          cas <- evalR as'
          let lcas = runravelToList cas
              las = runravelToList as
              lp = runravelToList p
          return $! foldl' df cx0 (zip3 lcas (init lp) las)
        FoldDR domsOD p as df _rf x0' as' -> do
          let width = rlength p - 1
              domsLen = V.length domsOD
              shn = shapeDelta x0'
          cx0 <- evalR x0'
          cas <- V.mapM evalRDynamicRanked as'
          let domsTo3 :: ADReady f
                      => Domains f -> (Domains f, f r n, Domains f)
              domsTo3 doms = ( V.take domsLen doms
                             , rfromD $ doms V.! domsLen
                             , V.drop (domsLen + 1) doms )
              domsF = V.concat [domsOD, V.singleton (odFromSh @r shn), domsOD]
          return $! rfoldD (\cx doms' ->
                              rletDomainsIn domsF doms' $ \doms ->
                                let (ca, x, a) = domsTo3 doms
                                in df cx (dmkDomains ca) x (dmkDomains a))
                           domsF
                           cx0
                           (V.concat [ cas
                                     , V.singleton
                                         (DynamicRanked $ rslice 0 width p)
                                     , as ])
        FoldDRC _domsOD p as df _rf x0' as' -> do
          cx0 <- evalR x0'
          cas <- V.mapM evalRDynamicRanked as'
          let lcas = map dmkDomains $ unravelDomains cas
              las = map dmkDomains $ unravelDomains as
              lp = runravelToList p
          return $! foldl' (\cx (ca, x, a) -> df cx ca x a)
                           cx0 (zip3 lcas (init lp) las)
        ScanR @rm @m @_ @_ @n1 p as df _rf x0' as' -> case rshape as of
          width :$ shm -> do
            let !_A1 = assert (rlength p == width + 1) ()
                shn = shapeDelta x0'
            cx0 <- evalR x0'
            cas <- evalR as'
            let domsTo3 :: ADReady f => Domains f -> (f rm m, f r n1, f rm m)
                domsTo3 doms = ( rfromD $ doms V.! 0
                               , rfromD $ doms V.! 1
                               , rfromD $ doms V.! 2 )
                domsF =
                  V.fromList
                    [odFromSh @rm shm, odFromSh @r shn, odFromSh @rm shm]
            return $! rscanD (\cx doms' ->
                                rletDomainsIn domsF doms' $ \doms ->
                                  let (ca, x, a) = domsTo3 doms
                                  in df cx ca x a)
                             domsF
                             cx0
                             (V.fromList
                                [ DynamicRanked cas
                                , DynamicRanked $ rslice 0 width p
                                , DynamicRanked as ])
          ZS -> error "evalR: impossible pattern needlessly required"
        ScanDR @_ @_ @n1 domsOD p as df _rf x0' as' -> do
          let width = rlength p - 1
              domsLen = V.length domsOD
              shn = shapeDelta x0'
          cx0 <- evalR x0'
          cas <- V.mapM evalRDynamicRanked as'
          let domsTo3 :: ADReady f
                      => Domains f -> (Domains f, f r n1, Domains f)
              domsTo3 doms = ( V.take domsLen doms
                             , rfromD $ doms V.! domsLen
                             , V.drop (domsLen + 1) doms )
              domsF = V.concat [domsOD, V.singleton (odFromSh @r shn), domsOD]
          return $! rscanD (\cx doms' ->
                              rletDomainsIn domsF doms' $ \doms ->
                                let (ca, x, a) = domsTo3 doms
                                in df cx (dmkDomains ca) x (dmkDomains a))
                           domsF
                           cx0
                           (V.concat [ cas
                                     , V.singleton
                                         (DynamicRanked $ rslice 0 width p)
                                     , as ])
        CastR d -> do
          t <- evalR d
          return $! rcast t

        SToR (RToS d) -> evalR d  -- no information lost, so no checks
        SToR d -> rfromS <$> evalS d

      evalS
        :: forall sh r. (Sh.Shape sh, GoodScalar r)
        => DeltaS shaped r sh -> ST s (shaped r sh)
      evalS = \case
        ZeroS -> return 0
        InputS (InputId i) ->
          if i < dimR
          then case params V.! i of
            DynamicRanked{} -> error "buildDerivative: DynamicRanked"
            DynamicShaped @r2 @sh2 e -> case sameShape @sh2 @sh of
              Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
                Just Refl -> return e
                _ -> error "buildDerivative: scalar mismatch"
              _ -> error "buildDerivative: shape mismatch"
            DynamicRankedDummy{} -> error "buildDerivative: DynamicRankedDummy"
            DynamicShapedDummy{} -> error "buildDerivative: DynamicShapedDummy"
          else error "buildDerivative: wrong index for an input"
        ScaleS k d -> (* k) <$> evalS d
        AddS d e -> liftM2 (+) (evalS d) (evalS e)
        LetS n d -> do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBindingS _) -> do
              dm <- readSTRef dMap
              case dm EM.! n of
                DynamicRanked{} -> error "buildDerivative: DynamicRanked"
                DynamicShaped @r2 @sh2 e -> case sameShape @sh2 @sh of
                  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
                    Just Refl -> return e
                    _ -> error "buildDerivative: scalar mismatch"
                  _ -> error "buildDerivative: shape mismatch"
                DynamicRankedDummy{} ->
                  error "buildDerivative: DynamicRankedDummy"
                DynamicShapedDummy{} ->
                  error "buildDerivative: DynamicShapedDummy"
            Nothing -> do
              cRaw <- evalS d
              ab <- readSTRef astBindings
              let (abShared, cShared) = sregister cRaw ab
              writeSTRef astBindings abShared
              nmNew <- readSTRef nMap
              writeSTRef nMap $! EM.insert n (DeltaBindingS d) nmNew
              dm <- readSTRef dMap
              writeSTRef dMap $! EM.insert n (DynamicShaped cShared) dm
              return cShared
            _ -> error "buildDerivative: corrupted nMap"

        IndexS d ix -> (`sindex` ix) <$> evalS d
        SumS d -> ssum <$> evalS d
        Sum0S ZeroS -> return 0
        Sum0S d -> ssum0 <$> evalS d
        Dot0S _ ZeroS -> return 0
        Dot0S v d -> sdot0 v <$> evalS d
        ScatterS d f -> do
          t <- evalS d
          return $! sscatter t f

        FromListS lsd -> do
          l <- mapM evalS lsd
          return $! sfromList l
        FromVectorS lsd -> do
          l <- V.mapM evalS lsd
          return $! sfromVector l
        ReplicateS d -> do
          t <- evalS d
          return $! sreplicate t
        AppendS d e -> liftM2 sappend (evalS d) (evalS e)
        SliceS @_ @i d -> sslice (Proxy @i) Proxy <$> evalS d
        ReverseS d -> sreverse <$> evalS d
        TransposeS @_ @perm d -> stranspose (Proxy @perm) <$> evalS d
        ReshapeS d -> sreshape <$> evalS d
        GatherS d f -> do
          t <- evalS d
          return $! sgather t f
        FoldS @rm @shm @k p as df _rf x0' as' -> do
          cx0 <- evalS x0'
          cas <- evalS as'
          let domsTo3 :: ADReadyS f
                      => Domains (RankedOf f) -> (f rm shm, f r sh, f rm shm)
              domsTo3 doms = ( sfromD $ doms V.! 0
                             , sfromD $ doms V.! 1
                             , sfromD $ doms V.! 2 )
              domsF =
                V.fromList
                  [odFromShS @rm @shm, odFromShS @r @sh, odFromShS @rm @shm]
          return $! sfoldD (\cx doms' ->
                              sletDomainsIn domsF doms' $ \doms ->
                                let (ca, x, a) = domsTo3 doms
                                in df cx ca x a)
                           domsF
                           cx0
                           (V.fromList
                              [ DynamicShaped cas
                              , DynamicShaped $ sslice (Proxy @0) (Proxy @k) p
                              , DynamicShaped as ])
        FoldSC p as df _rf x0' as' -> do
          cx0 <- evalS x0'
          cas <- evalS as'
          let lcas = sunravelToList cas
              las = sunravelToList as
              lp = sunravelToList p
          return $! foldl' df cx0 (zip3 lcas (init lp) las)
{-
        FoldDS domsOD p as df _rf x0' as' -> do
          let width = rlength p - 1
              domsLen = V.length domsOD
              shn = shapeDelta x0'
          cx0 <- evalR x0'
          cas <- V.mapM evalSDynamicShaped as'
          let domsTo3 :: ADReady f
                      => Domains f -> (Domains f, f r sh, Domains f)
              domsTo3 doms = ( V.take domsLen doms
                             , rfromD $ doms V.! domsLen
                             , V.drop (domsLen + 1) doms )
              domsF = V.concat [domsOD, V.singleton (odFromSh @r shn), domsOD]
          return $! rfoldD (\cx doms' ->
                              rletDomainsIn domsF doms' $ \doms ->
                                let (ca, x, a) = domsTo3 doms
                                in df cx (dmkDomains ca) x (dmkDomains a))
                           domsF
                           cx0
                           (V.concat [ cas
                                     , V.singleton
                                         (DynamicShaped $ rslice 0 width p)
                                     , as ])
-}
        FoldDSC _domsOD p as df _rf x0' as' -> do
          cx0 <- evalS x0'
          cas <- V.mapM evalSDynamicShaped as'
          let lcas = map dmkDomains $ unravelDomains cas
              las = map dmkDomains $ unravelDomains as
              lp = sunravelToList p
          return $! foldl' (\cx (ca, x, a) -> df cx ca x a)
                           cx0 (zip3 lcas (init lp) las)
{-
        ScanS @rm @m @_ @_ @n1 p as df _rf x0' as' -> case rshape as of
          width :$ shm -> do
            let !_A1 = assert (rlength p == width + 1) ()
                shn = shapeDelta x0'
            cx0 <- evalR x0'
            cas <- evalR as'
            let domsTo3 :: ADReady f => Domains f -> (f rm shm, f r sh1, f rm shm)
                domsTo3 doms = ( rfromD $ doms V.! 0
                               , rfromD $ doms V.! 1
                               , rfromD $ doms V.! 2 )
                domsF =
                  V.fromList
                    [odFromSh @rm shm, odFromSh @r shn, odFromSh @rm shm]
            return $! rscanD (\cx doms' ->
                                rletDomainsIn domsF doms' $ \doms ->
                                  let (ca, x, a) = domsTo3 doms
                                  in df cx ca x a)
                             domsF
                             cx0
                             (V.fromList
                                [ DynamicShaped cas
                                , DynamicShaped $ rslice 0 width p
                                , DynamicShaped as ])
          ZS -> error "evalR: impossible pattern needlessly required"
        ScanDS @_ @_ @n1 domsOD p as df _rf x0' as' -> do
          let width = rlength p - 1
              domsLen = V.length domsOD
              shn = shapeDelta x0'
          cx0 <- evalR x0'
          cas <- V.mapM evalSDynamicShaped as'
          let domsTo3 :: ADReady f
                      => Domains f -> (Domains f, f r sh1, Domains f)
              domsTo3 doms = ( V.take domsLen doms
                             , rfromD $ doms V.! domsLen
                             , V.drop (domsLen + 1) doms )
              domsF = V.concat [domsOD, V.singleton (odFromSh @r shn), domsOD]
          return $! rscanD (\cx doms' ->
                              rletDomainsIn domsF doms' $ \doms ->
                                let (ca, x, a) = domsTo3 doms
                                in df cx (dmkDomains ca) x (dmkDomains a))
                           domsF
                           cx0
                           (V.concat [ cas
                                     , V.singleton
                                         (DynamicShaped $ rslice 0 width p)
                                     , as ])
-}
        CastS d -> do
          t <- evalS d
          return $! scast t

        RToS (SToR @sh2 d) ->
          case sameShape @sh @sh2 of
            Just Refl -> evalS d
            _ -> error "buildDerivative: different shapes in RToS(SToR)"
        RToS d -> sfromR <$> evalR d

  -- A hack to fit both argument delta and, afterwards, the result in a type
  -- that does not reflect either.
  case deltaDt of
    DeltaDtR @_ @n _dt deltaTopLevel -> do
      c <- evalR deltaTopLevel
      let !cDelta = DeltaDtR c (ZeroR $ listShapeToShape
                                $ replicate (valueOf @n) 0)
      ab <- readSTRef astBindings
      return (ab, cDelta)
    DeltaDtS _dt deltaTopLevel -> do
      c <- evalS deltaTopLevel
      let !cDelta = DeltaDtS c ZeroS
      ab <- readSTRef astBindings
      return (ab, cDelta)


-- * Manually fixed Show intances

instance (KnownNat n0,
          GoodScalar r0,
          Show (IntOf @Nat ranked),
          Show
            (IntOf
               @[Nat]
               (ShapedOf @Nat ranked)),
          CRanked ranked Show,
          CShaped
            (ShapedOf @Nat ranked)
            Show,
          CShaped
            (DeltaS
               (ShapedOf @Nat ranked))
            Show) =>
         Show (DeltaR ranked r0 n0) where
  showsPrec a_adiH (ZeroR b1_adiI)
    = showParen
        (a_adiH >= 11)
        ((.)
           (showString "ZeroR ") (showsPrec 11 b1_adiI))
  showsPrec
    a_adiJ
    (InputR b1_adiK b2_adiL)
    = showParen
        (a_adiJ >= 11)
        ((.)
           (showString "InputR ")
           ((.)
              (showsPrec 11 b1_adiK)
              ((.) showSpace (showsPrec 11 b2_adiL))))
  showsPrec
    a_adiM
    (ScaleR b1_adiN b2_adiO)
    = showParen
        (a_adiM >= 11)
        ((.)
           (showString "ScaleR ")
           ((.)
              (showsPrec 11 b1_adiN)
              ((.) showSpace (showsPrec 11 b2_adiO))))
  showsPrec a_adiP (AddR b1_adiQ b2_adiR)
    = showParen
        (a_adiP >= 11)
        ((.)
           (showString "AddR ")
           ((.)
              (showsPrec 11 b1_adiQ)
              ((.) showSpace (showsPrec 11 b2_adiR))))
  showsPrec a_adiS (LetR b1_adiT b2_adiU)
    = showParen
        (a_adiS >= 11)
        ((.)
           (showString "LetR ")
           ((.)
              (showsPrec 11 b1_adiT)
              ((.) showSpace (showsPrec 11 b2_adiU))))
  showsPrec
    a_adiV
    (IndexR b1_adiW b2_adiX)
    = showParen
        (a_adiV >= 11)
        ((.)
           (showString "IndexR ")
           ((.)
              (showsPrec 11 b1_adiW)
              ((.) showSpace (showsPrec 11 b2_adiX))))
  showsPrec a_adiY (SumR b1_adiZ)
    = showParen
        (a_adiY >= 11)
        ((.)
           (showString "SumR ") (showsPrec 11 b1_adiZ))
  showsPrec a_adj0 (Sum0R b1_adj1)
    = showParen
        (a_adj0 >= 11)
        ((.)
           (showString "Sum0R ") (showsPrec 11 b1_adj1))
  showsPrec
    a_adj2
    (Dot0R b1_adj3 b2_adj4)
    = showParen
        (a_adj2 >= 11)
        ((.)
           (showString "Dot0R ")
           ((.)
              (showsPrec 11 b1_adj3)
              ((.) showSpace (showsPrec 11 b2_adj4))))
  showsPrec
    a_adj5
    (ScatterR b1_adj6 b2_adj7 b3_adj8)
    = showParen
        (a_adj5 >= 11)
        ((.)
           (showString "ScatterR ")
           ((.)
              (showsPrec 11 b1_adj6)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_adj7)
                    ((.)
                       showSpace (showsPrec 11 b3_adj8))))))
  showsPrec a_adj9 (FromListR b1_adja)
    = showParen
        (a_adj9 >= 11)
        ((.)
           (showString "FromListR ") (showsPrec 11 b1_adja))
  showsPrec a_adjb (FromVectorR b1_adjc)
    = showParen
        (a_adjb >= 11)
        ((.)
           (showString "FromVectorR ")
           (showsPrec 11 b1_adjc))
  showsPrec
    a_adjd
    (ReplicateR b1_adje b2_adjf)
    = showParen
        (a_adjd >= 11)
        ((.)
           (showString "ReplicateR ")
           ((.)
              (showsPrec 11 b1_adje)
              ((.) showSpace (showsPrec 11 b2_adjf))))
  showsPrec
    a_adjg
    (AppendR b1_adjh b2_adji)
    = showParen
        (a_adjg >= 11)
        ((.)
           (showString "AppendR ")
           ((.)
              (showsPrec 11 b1_adjh)
              ((.) showSpace (showsPrec 11 b2_adji))))
  showsPrec
    a_adjj
    (SliceR b1_adjk b2_adjl b3_adjm)
    = showParen
        (a_adjj >= 11)
        ((.)
           (showString "SliceR ")
           ((.)
              (showsPrec 11 b1_adjk)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_adjl)
                    ((.)
                       showSpace (showsPrec 11 b3_adjm))))))
  showsPrec a_adjn (ReverseR b1_adjo)
    = showParen
        (a_adjn >= 11)
        ((.)
           (showString "ReverseR ") (showsPrec 11 b1_adjo))
  showsPrec
    a_adjp
    (TransposeR b1_adjq b2_adjr)
    = showParen
        (a_adjp >= 11)
        ((.)
           (showString "TransposeR ")
           ((.)
              (showsPrec 11 b1_adjq)
              ((.) showSpace (showsPrec 11 b2_adjr))))
  showsPrec
    a_adjs
    (ReshapeR b1_adjt b2_adju)
    = showParen
        (a_adjs >= 11)
        ((.)
           (showString "ReshapeR ")
           ((.)
              (showsPrec 11 b1_adjt)
              ((.) showSpace (showsPrec 11 b2_adju))))
  showsPrec
    a_adjv
    (GatherR b1_adjw b2_adjx b3_adjy)
    = showParen
        (a_adjv >= 11)
        ((.)
           (showString "GatherR ")
           ((.)
              (showsPrec 11 b1_adjw)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_adjx)
                    ((.)
                       showSpace (showsPrec 11 b3_adjy))))))
  showsPrec
    a_adjz
    (FoldR b1_adjA b2_adjB _b3_adjC _b4_adjD b5_adjE
                              b6_adjF)
    = showParen
        (a_adjz >= 11)
        ((.)
           (showString "FoldR ")
           ((.)
              (showsPrec 11 b1_adjA)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_adjB)
                    ((.)
                       showSpace
                       ((.)
                          (showString "<forall function>")
                          ((.)
                             showSpace
                             ((.)
                                (showString "<forall function>")
                                ((.)
                                   showSpace
                                   ((.)
                                      (showsPrec 11 b5_adjE)
                                      ((.)
                                         showSpace
                                         (showsPrec 11 b6_adjF))))))))))))
  showsPrec
    a_adjG
    (FoldRC b1_adjH b2_adjI b3_adjJ b4_adjK b5_adjL
                               b6_adjM)
    = showParen
        (a_adjG >= 11)
        ((.)
           (showString "FoldRC ")
           ((.)
              (showsPrec 11 b1_adjH)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_adjI)
                    ((.)
                       showSpace
                       ((.)
                          (showsPrec 11 b3_adjJ)
                          ((.)
                             showSpace
                             ((.)
                                (showsPrec 11 b4_adjK)
                                ((.)
                                   showSpace
                                   ((.)
                                      (showsPrec 11 b5_adjL)
                                      ((.)
                                         showSpace
                                         (showsPrec 11 b6_adjM))))))))))))
  showsPrec
    a_adjN
    (FoldDR b1_adjO b2_adjP b3_adjQ _b4_adjR _b5_adjS
                               b6_adjT b7_adjU)
    = showParen
        (a_adjN >= 11)
        ((.)
           (showString "FoldDR ")
           ((.)
              (showsPrec 11 b1_adjO)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_adjP)
                    ((.)
                       showSpace
                       ((.)
                          (showsPrec 11 b3_adjQ)
                          ((.)
                             showSpace
                             ((.)
                                (showString "<forall function>")
                                ((.)
                                   showSpace
                                   ((.)
                                      (showString "<forall function>")
                                      ((.)
                                         showSpace
                                         ((.)
                                            (showsPrec 11 b6_adjT)
                                            ((.)
                                               showSpace
                                               (showsPrec 11 b7_adjU))))))))))))))
  showsPrec
    a_adjV
    (FoldDRC b1_adjW b2_adjX b3_adjY b4_adjZ b5_adk0
                                b6_adk1 b7_adk2)
    = showParen
        (a_adjV >= 11)
        ((.)
           (showString "FoldDRC ")
           ((.)
              (showsPrec 11 b1_adjW)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_adjX)
                    ((.)
                       showSpace
                       ((.)
                          (showsPrec 11 b3_adjY)
                          ((.)
                             showSpace
                             ((.)
                                (showsPrec 11 b4_adjZ)
                                ((.)
                                   showSpace
                                   ((.)
                                      (showsPrec 11 b5_adk0)
                                      ((.)
                                         showSpace
                                         ((.)
                                            (showsPrec 11 b6_adk1)
                                            ((.)
                                               showSpace
                                               (showsPrec 11 b7_adk2))))))))))))))
  showsPrec
    a_adk3
    (ScanR b1_adk4 b2_adk5 _b3_adk6 _b4_adk7 b5_adk8
                              b6_adk9)
    = showParen
        (a_adk3 >= 11)
        ((.)
           (showString "ScanR ")
           ((.)
              (showsPrec 11 b1_adk4)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_adk5)
                    ((.)
                       showSpace
                       ((.)
                          (showString "<forall function>")
                          ((.)
                             showSpace
                             ((.)
                                (showString "<forall function>")
                                ((.)
                                   showSpace
                                   ((.)
                                      (showsPrec 11 b5_adk8)
                                      ((.)
                                         showSpace
                                         (showsPrec 11 b6_adk9))))))))))))
  showsPrec
    a_adka
    (ScanDR b1_adkb b2_adkc b3_adkd _b4_adke _b5_adkf
                               b6_adkg b7_adkh)
    = showParen
        (a_adka >= 11)
        ((.)
           (showString "ScanDR ")
           ((.)
              (showsPrec 11 b1_adkb)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_adkc)
                    ((.)
                       showSpace
                       ((.)
                          (showsPrec 11 b3_adkd)
                          ((.)
                             showSpace
                             ((.)
                                (showString "<forall function>")
                                ((.)
                                   showSpace
                                   ((.)
                                      (showString "<forall function>")
                                      ((.)
                                         showSpace
                                         ((.)
                                            (showsPrec 11 b6_adkg)
                                            ((.)
                                               showSpace
                                               (showsPrec 11 b7_adkh))))))))))))))
  showsPrec a_adki (CastR b1_adkj)
    = showParen
        (a_adki >= 11)
        ((.)
           (showString "CastR ") (showsPrec 11 b1_adkj))
  showsPrec a_adkk (SToR b1_adkl)
    = showParen
        (a_adkk >= 11)
        ((.)
           (showString "SToR ") (showsPrec 11 b1_adkl))

instance (ShapedOf (RankedOf shaped) ~ shaped,
          Sh.Shape sh0,
          GoodScalar r0,
          Show
            (IntOf
               @Nat
               (RankedOf @[Nat] shaped)),
          Show
            (IntOf @[Nat] shaped),
          CRanked
            (RankedOf @[Nat] shaped)
            Show,
          CShaped shaped Show,
          CRanked
            (DeltaR
               (RankedOf @[Nat] shaped))
            Show) =>
         Show (DeltaS shaped r0 sh0) where
  showsPrec _ ZeroS
    = showString "ZeroS"
  showsPrec a_adtF (InputS b1_adtG)
    = showParen
        (a_adtF >= 11)
        ((.)
           (showString "InputS ") (showsPrec 11 b1_adtG))
  showsPrec
    a_adtH
    (ScaleS b1_adtI b2_adtJ)
    = showParen
        (a_adtH >= 11)
        ((.)
           (showString "ScaleS ")
           ((.)
              (showsPrec 11 b1_adtI)
              ((.) showSpace (showsPrec 11 b2_adtJ))))
  showsPrec a_adtK (AddS b1_adtL b2_adtM)
    = showParen
        (a_adtK >= 11)
        ((.)
           (showString "AddS ")
           ((.)
              (showsPrec 11 b1_adtL)
              ((.) showSpace (showsPrec 11 b2_adtM))))
  showsPrec a_adtN (LetS b1_adtO b2_adtP)
    = showParen
        (a_adtN >= 11)
        ((.)
           (showString "LetS ")
           ((.)
              (showsPrec 11 b1_adtO)
              ((.) showSpace (showsPrec 11 b2_adtP))))
  showsPrec
    a_adtQ
    (IndexS b1_adtR b2_adtS)
    = showParen
        (a_adtQ >= 11)
        ((.)
           (showString "IndexS ")
           ((.)
              (showsPrec 11 b1_adtR)
              ((.) showSpace (showsPrec 11 b2_adtS))))
  showsPrec a_adtT (SumS b1_adtU)
    = showParen
        (a_adtT >= 11)
        ((.)
           (showString "SumS ") (showsPrec 11 b1_adtU))
  showsPrec a_adtV (Sum0S b1_adtW)
    = showParen
        (a_adtV >= 11)
        ((.)
           (showString "Sum0S ") (showsPrec 11 b1_adtW))
  showsPrec
    a_adtX
    (Dot0S b1_adtY b2_adtZ)
    = showParen
        (a_adtX >= 11)
        ((.)
           (showString "Dot0S ")
           ((.)
              (showsPrec 11 b1_adtY)
              ((.) showSpace (showsPrec 11 b2_adtZ))))
  showsPrec
    a_adu0
    (ScatterS b1_adu1 b2_adu2)
    = showParen
        (a_adu0 >= 11)
        ((.)
           (showString "ScatterS ")
           ((.)
              (showsPrec 11 b1_adu1)
              ((.) showSpace (showsPrec 11 b2_adu2))))
  showsPrec a_adu3 (FromListS b1_adu4)
    = showParen
        (a_adu3 >= 11)
        ((.)
           (showString "FromListS ") (showsPrec 11 b1_adu4))
  showsPrec a_adu5 (FromVectorS b1_adu6)
    = showParen
        (a_adu5 >= 11)
        ((.)
           (showString "FromVectorS ")
           (showsPrec 11 b1_adu6))
  showsPrec a_adu7 (ReplicateS b1_adu8)
    = showParen
        (a_adu7 >= 11)
        ((.)
           (showString "ReplicateS ")
           (showsPrec 11 b1_adu8))
  showsPrec
    a_adu9
    (AppendS b1_adua b2_adub)
    = showParen
        (a_adu9 >= 11)
        ((.)
           (showString "AppendS ")
           ((.)
              (showsPrec 11 b1_adua)
              ((.) showSpace (showsPrec 11 b2_adub))))
  showsPrec a_aduc (SliceS b1_adud)
    = showParen
        (a_aduc >= 11)
        ((.)
           (showString "SliceS ") (showsPrec 11 b1_adud))
  showsPrec a_adue (ReverseS b1_aduf)
    = showParen
        (a_adue >= 11)
        ((.)
           (showString "ReverseS ") (showsPrec 11 b1_aduf))
  showsPrec a_adug (TransposeS b1_aduh)
    = showParen
        (a_adug >= 11)
        ((.)
           (showString "TransposeS ")
           (showsPrec 11 b1_aduh))
  showsPrec a_adui (ReshapeS b1_aduj)
    = showParen
        (a_adui >= 11)
        ((.)
           (showString "ReshapeS ") (showsPrec 11 b1_aduj))
  showsPrec
    a_aduk
    (GatherS b1_adul b2_adum)
    = showParen
        (a_aduk >= 11)
        ((.)
           (showString "GatherS ")
           ((.)
              (showsPrec 11 b1_adul)
              ((.) showSpace (showsPrec 11 b2_adum))))
  showsPrec
    a_adun
    (FoldS b1_aduo b2_adup _b3_aduq _b4_adur b5_adus
                              b6_adut)
    = showParen
        (a_adun >= 11)
        ((.)
           (showString "FoldS ")
           ((.)
              (showsPrec 11 b1_aduo)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_adup)
                    ((.)
                       showSpace
                       ((.)
                          (showString "<forall function>")
                          ((.)
                             showSpace
                             ((.)
                                (showString "<forall function>")
                                ((.)
                                   showSpace
                                   ((.)
                                      (showsPrec 11 b5_adus)
                                      ((.)
                                         showSpace
                                         (showsPrec 11 b6_adut))))))))))))
  showsPrec
    a_aduu
    (FoldSC b1_aduv b2_aduw b3_adux b4_aduy b5_aduz
                               b6_aduA)
    = showParen
        (a_aduu >= 11)
        ((.)
           (showString "FoldSC ")
           ((.)
              (showsPrec 11 b1_aduv)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_aduw)
                    ((.)
                       showSpace
                       ((.)
                          (showsPrec 11 b3_adux)
                          ((.)
                             showSpace
                             ((.)
                                (showsPrec 11 b4_aduy)
                                ((.)
                                   showSpace
                                   ((.)
                                      (showsPrec 11 b5_aduz)
                                      ((.)
                                         showSpace
                                         (showsPrec 11 b6_aduA))))))))))))
  showsPrec
    a_aduB
    (FoldDS b1_aduC b2_aduD b3_aduE _b4_aduF _b5_aduG
                               b6_aduH b7_aduI)
    = showParen
        (a_aduB >= 11)
        ((.)
           (showString "FoldDS ")
           ((.)
              (showsPrec 11 b1_aduC)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_aduD)
                    ((.)
                       showSpace
                       ((.)
                          (showsPrec 11 b3_aduE)
                          ((.)
                             showSpace
                             ((.)
                                (showString "<forall function>")
                                ((.)
                                   showSpace
                                   ((.)
                                      (showString "<forall function>")
                                      ((.)
                                         showSpace
                                         ((.)
                                            (showsPrec 11 b6_aduH)
                                            ((.)
                                               showSpace
                                               (showsPrec 11 b7_aduI))))))))))))))
  showsPrec
    a_aduJ
    (FoldDSC b1_aduK b2_aduL b3_aduM b4_aduN b5_aduO
                                b6_aduP b7_aduQ)
    = showParen
        (a_aduJ >= 11)
        ((.)
           (showString "FoldDSC ")
           ((.)
              (showsPrec 11 b1_aduK)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_aduL)
                    ((.)
                       showSpace
                       ((.)
                          (showsPrec 11 b3_aduM)
                          ((.)
                             showSpace
                             ((.)
                                (showsPrec 11 b4_aduN)
                                ((.)
                                   showSpace
                                   ((.)
                                      (showsPrec 11 b5_aduO)
                                      ((.)
                                         showSpace
                                         ((.)
                                            (showsPrec 11 b6_aduP)
                                            ((.)
                                               showSpace
                                               (showsPrec 11 b7_aduQ))))))))))))))
  showsPrec
    a_aduR
    (ScanS b1_aduS b2_aduT _b3_aduU _b4_aduV b5_aduW
                              b6_aduX)
    = showParen
        (a_aduR >= 11)
        ((.)
           (showString "ScanS ")
           ((.)
              (showsPrec 11 b1_aduS)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_aduT)
                    ((.)
                       showSpace
                       ((.)
                          (showString "<forall function>")
                          ((.)
                             showSpace
                             ((.)
                                (showString "<forall function>")
                                ((.)
                                   showSpace
                                   ((.)
                                      (showsPrec 11 b5_aduW)
                                      ((.)
                                         showSpace
                                         (showsPrec 11 b6_aduX))))))))))))
  showsPrec
    a_aduY
    (ScanDS b1_aduZ b2_adv0 b3_adv1 _b4_adv2 _b5_adv3
                               b6_adv4 b7_adv5)
    = showParen
        (a_aduY >= 11)
        ((.)
           (showString "ScanDS ")
           ((.)
              (showsPrec 11 b1_aduZ)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_adv0)
                    ((.)
                       showSpace
                       ((.)
                          (showsPrec 11 b3_adv1)
                          ((.)
                             showSpace
                             ((.)
                                (showString "<forall function>")
                                ((.)
                                   showSpace
                                   ((.)
                                      (showString "<forall function>")
                                      ((.)
                                         showSpace
                                         ((.)
                                            (showsPrec 11 b6_adv4)
                                            ((.)
                                               showSpace
                                               (showsPrec 11 b7_adv5))))))))))))))
  showsPrec a_adv6 (CastS b1_adv7)
    = showParen
        (a_adv6 >= 11)
        ((.)
           (showString "CastS ") (showsPrec 11 b1_adv7))
  showsPrec a_adv8 (RToS b1_adv9)
    = showParen
        (a_adv8 >= 11)
        ((.)
           (showString "RToS ") (showsPrec 11 b1_adv9))
