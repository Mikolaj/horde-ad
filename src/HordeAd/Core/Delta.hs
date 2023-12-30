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
import           Data.List
  (foldl', mapAccumR, scanl', sort, transpose, zip4, zipWith4, zipWith5)
import           Data.List.Index (ifoldl')
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy (Proxy))
import           Data.STRef (newSTRef, readSTRef, writeSTRef)
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits
  (KnownNat, Nat, SomeNat (..), sameNat, someNatVal, type (+), type (<=))
import           Text.Show.Functions ()
import           Type.Reflection (TypeRep, typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances
  (matchingRank, sameShape, trustMeThisIsAPermutation)
import HordeAd.Util.ShapedList (ShapedList (..))
import HordeAd.Util.SizedIndex

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
        => (ranked rn n -> ranked rm m -> ranked rn n)
        -> ranked rn n -> ranked rm (1 + m)
        -> (ranked rn n -> (ranked rm m, ranked rn n, ranked rm m)
            -> ranked rn n)
        -> (ranked rn n -> (ranked rn n, ranked rm m)
            -> (ranked rn n, ranked rm m))
        -> DeltaR ranked rn n
        -> DeltaR ranked rm (1 + m)
        -> DeltaR ranked rn n
  ScanR :: (GoodScalar rm, KnownNat m)
        => (ranked rn n -> ranked rm m -> ranked rn n)
        -> ranked rn n -> ranked rm (1 + m)
        -> (ranked rn n -> (ranked rm m, ranked rn n, ranked rm m)
            -> ranked rn n)
        -> (ranked rn n -> (ranked rn n, ranked rm m)
            -> (ranked rn n, ranked rm m))
        -> DeltaR ranked rn n
        -> DeltaR ranked rm (1 + m)
        -> DeltaR ranked rn (1 + n)
  Scan2R :: (GoodScalar rm, KnownNat m, GoodScalar rp, KnownNat p)
         => (ranked rn n -> (ranked rm m, ranked rp p) -> ranked rn n)
         -> ranked rn n -> ranked rm (1 + m) -> ranked rp (1 + p)
         -> (ranked rn n -> ( ranked rm m, ranked rp p, ranked rn n
                            , ranked rm m, ranked rp p )
             -> ranked rn n)
         -> (ranked rn n -> (ranked rn n, ranked rm m, ranked rp p)
             -> (ranked rn n, (ranked rm m, ranked rp p)))
         -> DeltaR ranked rn n
         -> DeltaR ranked rm (1 + m)
         -> DeltaR ranked rp (1 + p)
         -> DeltaR ranked rn (1 + n)
  ScanDR :: (ranked rn n -> Domains ranked -> ranked rn n)
         -> ranked rn n -> Domains ranked  -- one rank higher
         -> (ranked rn n -> (Domains ranked, ranked rn n, Domains ranked)
             -> ranked rn n)
         -> (ranked rn n -> (ranked rn n, Domains ranked)
             -> (ranked rn n, Domains ranked))
         -> DeltaR ranked rn n
         -> Domains (DeltaR ranked)  -- one rank higher
         -> DeltaR ranked rn (1 + n)
    -- ^ Fold over the outermost dimension of a tensor. The function,
    -- in the first argument, should be strict in the accumulator.
  CastR :: (GoodScalar r1, RealFrac r1, RealFrac r2)
        => DeltaR ranked r1 n -> DeltaR ranked r2 n
  SToR :: forall sh r ranked. Sh.Shape sh
       => DeltaS (ShapedOf ranked) r sh
       -> DeltaR ranked r (Sh.Rank sh)

deriving instance ( KnownNat n0, GoodScalar r0
                  , Show (IntOf ranked)
                  , Show (IntOf (ShapedOf ranked))
                  , CRanked ranked Show
                  , CShaped (ShapedOf ranked) Show
                  , CShaped (DeltaS (ShapedOf ranked)) Show )
                  => Show (DeltaR ranked r0 n0)

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
        => (shaped rn sh -> shaped rm shm -> shaped rn sh)
        -> shaped rn sh -> shaped rm (k ': shm)
        -> (shaped rn sh -> (shaped rm shm, shaped rn sh, shaped rm shm)
            -> shaped rn sh)
        -> (shaped rn sh -> (shaped rn sh, shaped rm shm)
            -> (shaped rn sh, shaped rm shm))
        -> DeltaS shaped rn sh
        -> DeltaS shaped rm (k ': shm)
        -> DeltaS shaped rn sh
  CastS :: (GoodScalar r1, RealFrac r1, RealFrac r2)
        => DeltaS shaped r1 sh -> DeltaS shaped r2 sh
  RToS :: forall sh r shaped. KnownNat (Sh.Rank sh)
       => DeltaR (RankedOf shaped) r (Sh.Rank sh)
       -> DeltaS shaped r sh

deriving instance ( Sh.Shape sh0, GoodScalar r0
                  , Show (IntOf (RankedOf shaped))
                  , Show (IntOf shaped)
                  , CRanked (RankedOf shaped) Show
                  , CShaped shaped Show
                  , CRanked (DeltaR (RankedOf shaped)) Show )
                  => Show (DeltaS shaped r0 sh0)

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
  FoldR _f x0 _as _df _rf _x0' _as' -> rshape x0
  ScanR _f x0 as _df _rf _x0' _as' -> rlength as :$ rshape x0
  Scan2R _f x0 as _bs _df _rf _x0' _as' _bs' -> rlength as :$ rshape x0
  ScanDR _f x0 as _df _rf _x0' _as' -> case V.unsnoc as of
    Nothing -> error "shapeDelta: empty domains"
    Just (_, d) -> length (shapeDynamic d) :$ rshape x0
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

instance ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
         , RankedOf (ShapedOf ranked) ~ ranked, RankedOf ranked ~ ranked )
         => DualPart @Nat ranked where
  type Dual ranked = DeltaR ranked
  reverseDervative = gradientDtR
  forwardDerivative = derivativeFromDeltaR

gradientDtR
  :: ( KnownNat y, GoodScalar r
     , RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => DomainsOD
  -> ranked r y -> Maybe (ranked r y) -> DeltaR ranked r y
  -> (AstBindingsD ranked, Domains ranked)
gradientDtR !parameters0 value !mdt !deltaTopLevel =
  let dt = fromMaybe (rreplicate0N (rshape value) 1) mdt
      deltaDt = DeltaDtR dt deltaTopLevel
  in gradientFromDelta parameters0 deltaDt
{-# SPECIALIZE gradientDtR
  :: KnownNat y
  => DomainsOD -> Flip OR.Array Double y -> Maybe (Flip OR.Array Double y)
  -> DeltaR (Flip OR.Array) Double y
  -> (AstBindingsD (Flip OR.Array), Domains (Flip OR.Array) ) #-}
{- TODO: this causes a cyclic dependency:
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
     ( KnownNat n, GoodScalar r
     , RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => Int -> DeltaR ranked r n -> Domains ranked
  -> (AstBindingsD ranked, ranked r n)
derivativeFromDeltaR dim deltaTopLevel ds =
  let dummyZero = rzero $ listShapeToShape $ replicate (valueOf @n) 1
  in case runST $ buildDerivative dim (DeltaDtR dummyZero deltaTopLevel) ds of
    (l, DeltaDtR @_ @n2 res _) -> case sameNat (Proxy @n) (Proxy @n2) of
      Just Refl -> (l, res)
      _ -> error "derivativeFromDeltaR"
    (_, DeltaDtS{}) -> error "derivativeFromDeltaR"

instance ( RankedTensor (RankedOf shaped), ShapedTensor shaped
         , ShapedOf (RankedOf shaped) ~ shaped )
         => DualPart @[Nat] shaped where
  type Dual shaped = DeltaS shaped
  reverseDervative parameters0 _ = gradientDtS parameters0
  forwardDerivative = derivativeFromDeltaS

gradientDtS
  :: forall shaped r y.
     ( Sh.Shape y, GoodScalar r
     , RankedTensor (RankedOf shaped), ShapedTensor shaped
     , ShapedOf (RankedOf shaped) ~ shaped )
  => DomainsOD
  -> Maybe (shaped r y) -> DeltaS shaped r y
  -> (AstBindingsD (RankedOf shaped), Domains (RankedOf shaped))
gradientDtS !parameters0 !mdt !deltaTopLevel =
  let dt = fromMaybe 1 mdt
      deltaDt = DeltaDtS dt deltaTopLevel
  in gradientFromDelta parameters0 deltaDt
{-# SPECIALIZE gradientDtS
  :: Sh.Shape y
  => DomainsOD -> Maybe (Flip OS.Array Double y)
  -> DeltaS (Flip OS.Array) Double y
  -> (AstBindingsD (Flip OR.Array), Domains (Flip OR.Array)) #-}
{- TODO: this causes a cyclic dependency:
{-# SPECIALIZE gradientDtS
  :: Sh.Shape y
  => DomainsOD -> Maybe (AstShaped PrimalSpan Double y)
  -> DeltaS (AstShaped PrimalSpan) Double y
  -> ( AstBindingsD (DynamicTensor (AstShaped PrimalSpan))
     , Domains (DynamicTensor (AstShaped PrimalSpan)) ) #-}
-}

derivativeFromDeltaS
  :: forall shaped r sh.
     ( Sh.Shape sh, GoodScalar r
     , RankedTensor (RankedOf shaped), ShapedTensor shaped
     , ShapedOf (RankedOf shaped) ~ shaped )
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
     ( GoodScalar r, RankedTensor ranked, ShapedTensor shaped
     , ShapedOf ranked ~ shaped, RankedOf shaped ~ ranked )
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
{-# SPECIALIZE gradientFromDelta
  :: DomainsOD -> DeltaDt (Flip OR.Array) (Flip OS.Array) Double
  -> (AstBindingsD (Flip OR.Array), DomainsOD) #-}
{- TODO: this causes a cyclic dependency:
{-# SPECIALIZE gradientFromDelta
  :: DomainsOD -> DeltaDt (AstRanked PrimalSpan) (AstShaped PrimalSpan) Double
  -> (AstBindingsD (AstRanked PrimalSpan), Domains (AstDynamic PrimalSpan)) #-}
-}

buildFinMaps
  :: forall ranked shaped r0.
     ( GoodScalar r0, RankedTensor ranked, ShapedTensor shaped
     , ShapedOf ranked ~ shaped, RankedOf shaped ~ ranked )
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
      evalR
        :: forall n r. (KnownNat n, GoodScalar r)
        => EvalState ranked shaped
        -> ranked r n -> DeltaR ranked r n
        -> EvalState ranked shaped
      evalR !s !c = let (abShared, cShared) = rregister c (astBindings s)
                        sShared = s {astBindings = abShared}
                    in \case
        ZeroR{} -> s
        InputR _ i -> s {iMap = EM.adjust (raddDynamic c) i $ iMap s}
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
                s {dMap = EM.adjust (raddDynamic c) n $ dMap s}
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

        FromListR ld ->
          ifoldl' (\ !s2 i d2 ->
            evalR s2 (rindex cShared (fromIntegral i :. ZI)) d2) sShared ld
        FromVectorR ld ->
          V.ifoldl' (\ !s2 i d2 ->
            evalR s2 (rindex cShared (fromIntegral i :. ZI)) d2) sShared ld
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
{-      FoldR @rm @m f x0 as _df rf x0' as' ->
          let p :: [ranked r n]
              p = scanl' f x0 las
              las :: [ranked rm m]
              las = runravelToList as
              rg :: ranked r n
                 -> [(ranked r n, ranked rm m)]
                 -> (ranked r n, [ranked rm m])
              rg = mapAccumR rf
              (cx0, cas) = rg cShared (zip (init p) las)
              s2 = evalR sShared cx0 x0'
          in evalR s2 (rfromList cas) as' -}
        FoldR @rm @m f x0 as _df rf x0' as' ->
          let p :: [ranked r n]
              p = scanl' f x0 las
              las :: [ranked rm m]
              las = runravelToList as
              crs :: [ranked r n]
              crs = scanr (\(x, a) cr -> fst $ rf cr (x, a))
                          cShared (zip (init p) las)
              rg :: [ranked r n] -> [ranked r n] -> [ranked rm m]
                 -> [ranked rm m]
              rg = zipWith3 (\cr x a -> snd $ rf cr (x, a))
              cas = rg (drop 1 crs) (init p) las
              s2 = evalR sShared (crs !! 0) x0'
          in evalR s2 (rfromList cas) as'
{-      ScanR @rm @m @_ @_ @n1 f x0 as _df rf x0' as' ->  -- n1 ~ n - 1
          let cxs :: [ranked r n1]
              cxs = runravelToList cShared
              p :: [ranked r n1]
              p = scanl' f x0 las
              las :: [ranked rm m]
              las = runravelToList as
              rg :: ranked r n1
                 -> [(ranked r n1, ranked r n1, ranked rm m)]
                 -> (ranked r n1, [ranked rm m])
              rg = mapAccumR $ \cr (cx, x, a) -> rf (cr + cx) (x, a)
              (cx0, cas) = rg (rzero $ rshape x0) (zip3 cxs (init p) las)
              s2 = evalR sShared cx0 x0'
          in evalR s2 (rfromList cas) as' -}
        ScanR @rm @m @_ @_ @n1 f x0 as _df rf x0' as' ->  -- n1 ~ n - 1
          let cxs :: [ranked r n1]
              cxs = runravelToList cShared
              p :: [ranked r n1]
              p = scanl' f x0 las
              las :: [ranked rm m]
              las = runravelToList as
              crs :: [ranked r n1]
              crs = scanr (\(cx, x, a) cr -> fst $ rf (cr + cx) (x, a))
                          (rzero $ rshape x0) (zip3 cxs (init p) las)
              rg :: [ranked r n1] -> [ranked r n1] -> [ranked r n1]
                 -> [ranked rm m]
                 -> [ranked rm m]
              rg = zipWith4 (\cr cx x a -> snd $ rf (cr + cx) (x, a))
              cas = rg (drop 1 crs) cxs (init p) las
              s2 = evalR sShared (crs !! 0) x0'
          in evalR s2 (rfromList cas) as'
        Scan2R @rm @m @rp @p @_ @_ @n1 f x0 as bs _df rf x0' as' bs' ->
          let cxs :: [ranked r n1]
              cxs = runravelToList cShared
              p :: [ranked r n1]
              p = scanl' f x0 (zip las lbs)
              las :: [ranked rm m]
              las = runravelToList as
              lbs :: [ranked rp p]
              lbs = runravelToList bs
              crs :: [ranked r n1]
              crs = scanr (\(cx, x, a, b) cr -> fst $ rf (cr + cx) (x, a, b))
                          (rzero $ rshape x0) (zip4 cxs (init p) las lbs)
              rg :: [ranked r n1] -> [ranked r n1] -> [ranked r n1]
                 -> [ranked rm m] -> [ranked rp p]
                 -> [(ranked rm m, ranked rp p)]
              rg = zipWith5 (\cr cx x a b -> snd $ rf (cr + cx) (x, a, b))
              (cas, cbs) = unzip $ rg (drop 1 crs) cxs (init p) las lbs
              s2 = evalR sShared (crs !! 0) x0'
              s3 = evalR s2 (rfromList cas) as'
          in evalR s3 (rfromList cbs) bs'
        ScanDR @_ @_ @n1 f x0 as _df rf x0' as' ->  -- n1 ~ n - 1
          let cxs :: [ranked r n1]
              cxs = runravelToList cShared
              ps :: [ranked r n1]
              ps = scanl' f x0 las
              unravelDynamicRanked
                :: DynamicTensor ranked -> [DynamicTensor ranked]
              unravelDynamicRanked (DynamicRanked @rp @p t) =
                case someNatVal $ valueOf @p - 1 of
                  Just (SomeNat @p1 _) ->
                    gcastWith (unsafeCoerce Refl :: p :~: 1 + p1 ) $
                    map (DynamicRanked @rp @p1) $ runravelToList t
                  Nothing -> error "unravelDynamicRanked: scalars in domain"
              unravelDynamicRanked DynamicShaped{} =
                error "unravelDynamicRanked: DynamicShaped"
              unravelDynamicRanked (DynamicRankedDummy @rp @sh _ _) =
                withListShape (Sh.shapeT @sh) $ \(sh :: ShapeInt p) ->
                  case someNatVal $ valueOf @p - 1 of
                    Just (SomeNat @p1 _) ->
                      gcastWith (unsafeCoerce Refl :: p :~: 1 + p1 ) $
                      map (DynamicRanked @rp @p1) $ runravelToList (rzero sh)
                    Nothing -> error "unravelDynamicRanked: scalars in domain"
              unravelDynamicRanked DynamicShapedDummy{} =
                error "unravelDynamicRanked: DynamicShapedDummy"
              unravelDomains
                :: Domains ranked  -- each tensor has outermost dimension size p
                -> [Domains ranked]  -- p domains; each tensor of one rank lower
              unravelDomains = map V.fromList . transpose
                               . map unravelDynamicRanked . V.toList
              ravelDynamicRanked  -- the inverse of unravelDynamicRanked
                :: [DynamicTensor ranked] -> DynamicTensor ranked
              ravelDynamicRanked ld = case ld of
                [] -> error "ravelDynamicRanked: empty list"
                d : _ -> case ( someNatVal
                                $ toInteger (length $ shapeDynamic d)
                              , scalarDynamic d ) of
                  (Just (SomeNat @p1 _), typeReprp :: TypeRep rp) ->
                    let g :: DynamicTensor ranked -> ranked rp p1
                        g (DynamicRanked @rq @q t)
                          | Just Refl <- sameNat (Proxy @q) (Proxy @p1)
                          , Just Refl <- testEquality (typeRep @rq)
                                                      typeReprp = t
                        g DynamicShaped{} =
                          error "ravelDynamicRanked: DynamicShaped"
                        g (DynamicRankedDummy @rq @sh _ _)
                          | Just Refl <- matchingRank @sh @p1
                          , Just Refl <- testEquality (typeRep @rq)
                                                      typeReprp =
                            withListShape (Sh.shapeT @sh)
                            $ \(sh :: ShapeInt q1) ->
                                case sameNat (Proxy @q1) (Proxy @p1) of
                                  Just Refl -> rzero sh
                                  Nothing ->
                                    error "ravelDynamicRanked: wrong rank"
                        g DynamicShapedDummy{} =
                          error "ravelDynamicRanked: DynamicShapedDummy"
                        g _ = error "ravelDynamicRanked: wrong scalar or rank"
                    in DynamicRanked @r $ rfromList $ map g ld
                  _ -> error "ravelDynamicRanked: impossible someNatVal"
              ravelDomains  -- the inverse of unravelDomains
                :: [Domains ranked]
                -> Domains ranked
              ravelDomains = V.fromList . map ravelDynamicRanked
                             . transpose . map V.toList
              las :: [Domains ranked]
              las = unravelDomains as
              crs :: [ranked r n1]
              crs = scanr (\(cx, x, a) cr -> fst $ rf (cr + cx) (x, a))
                          (rzero $ rshape x0) (zip3 cxs (init ps) las)
              rg :: [ranked r n1] -> [ranked r n1] -> [ranked r n1]
                 -> [Domains ranked]
                 -> [Domains ranked]
              rg = zipWith4 (\cr cx x a -> snd $ rf (cr + cx) (x, a))
              cas = rg (drop 1 crs) cxs (init ps) las
              s2 = evalR sShared (crs !! 0) x0'
              evalRDynamicRanked
                :: EvalState ranked shaped
                -> (DynamicTensor ranked, DynamicTensor (DeltaR ranked))
                -> EvalState ranked shaped
              evalRDynamicRanked s3 ( DynamicRanked @rp @p t
                                    , DynamicRanked @rq @q d )
                | Just Refl <- sameNat (Proxy @q) (Proxy @p)
                , Just Refl <- testEquality (typeRep @rp) (typeRep @rq) =
                    evalR s3 t d
              evalRDynamicRanked _ _ =
                error "evalRDynamicRanked: unexpected constructor"
          in V.foldl' evalRDynamicRanked s2 $ V.zip (ravelDomains cas) as'
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
        InputS i -> s {iMap = EM.adjust (saddDynamic c) i $ iMap s}
        ScaleS k d -> evalS s (k * c) d
        AddS d e -> evalS (evalS sShared cShared d) cShared e
        LetS n d ->
          assert (case d of
                    ZeroS -> False
                    LetS{} -> False  -- wasteful and nonsensical
                    _ -> True)
          $ case EM.lookup n $ nMap s of
              Just (DeltaBindingS _) ->
                s {dMap = EM.adjust (saddDynamic c) n $ dMap s}
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
        FoldS f x0 as _df rf x0' as' ->
          let las = sunravelToList as
              p = scanl' f x0 las
              (cx0, cas) = mapAccumR rf cShared (zip (init p) las)
              s2 = evalS sShared cx0 x0'
          in evalS s2 (sfromList cas) as'
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
{-# SPECIALIZE buildFinMaps
  :: EvalState (Flip OR.Array) (Flip OS.Array) -> DeltaDt (Flip OR.Array) (Flip OS.Array) Double -> EvalState (Flip OR.Array) (Flip OS.Array) #-}
{- TODO: this causes a cyclic dependency:
{-# SPECIALIZE buildFinMaps
  :: EvalState (AstRanked PrimalSpan) (AstShaped PrimalSpan) -> DeltaDt (AstRanked PrimalSpan) (AstShaped PrimalSpan) Double -> EvalState (AstRanked PrimalSpan) (AstShaped PrimalSpan) #-}
-}


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
     ( GoodScalar r0, RankedTensor ranked, ShapedTensor shaped
     , ShapedOf ranked ~ shaped, RankedOf shaped ~ ranked )
  => Int -> DeltaDt ranked shaped r0 -> Domains ranked
  -> ST s (AstBindingsD ranked, DeltaDt ranked shaped r0)
buildDerivative dimR deltaDt params = do
  dMap <- newSTRef EM.empty
  nMap <- newSTRef EM.empty
  astBindings <- newSTRef []
  let evalR
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
        FoldR f x0 as df _rf x0' as' -> do
          cx0 <- evalR x0'
          cas <- evalR as'
          let lcas = runravelToList cas
              las = runravelToList as
              p = scanl' f x0 las
          return $! foldl' df cx0 (zip3 lcas (init p) las)
        ScanR f x0 as df _rf x0' as' -> do
          cx0 <- evalR x0'
          cas <- evalR as'
          let lcas = runravelToList cas
              las = runravelToList as
              p = scanl' f x0 las
          return $! rfromList $ scanl' df cx0 (zip3 lcas (init p) las)
        Scan2R{} -> undefined
        ScanDR{} -> undefined
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
        FoldS f x0 as df _rf x0' as' -> do
          cx0 <- evalS x0'
          cas <- evalS as'
          let lcas = sunravelToList cas
              las = sunravelToList as
              p = scanl' f x0 las
          return $! foldl' df cx0 (zip3 lcas (init p) las)
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
