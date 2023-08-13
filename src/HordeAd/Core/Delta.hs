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
    DeltaR (..), DeltaS (..), DeltaD (..)
  , -- * Delta expression identifiers
    NodeId (..), InputId, toInputId
  , -- * Evaluation of the delta expressions
    DualPart(..), DeltaDt (..)
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (liftM2)
import           Control.Monad.ST.Strict (ST, runST)
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Internal.Shape as OS
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Kind (Constraint, Type)
import           Data.List (foldl', sort)
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
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Ast
import           HordeAd.Core.TensorAst ()
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (matchingRank, sameShape, trustMeThisIsAPermutation)
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
--
-- This is the grammar of delta-expressions corresponding to ranked tensors.
-- The comments refer to the ordinary (forward) semantics of the terms,
-- as given in @buildDerivative@. Evaluating the terms backwards
-- (transposing the represented linear map) in order to compute gradients
-- provides a different semantics.
data DeltaR :: RankedTensorKind -> ShapedTensorKind -> RankedTensorKind where
  ZeroR :: ShapeInt n -> DeltaR ranked shaped r n
    -- ^ the shape is required for @shapeDelta@ and forward derivative
  InputR :: forall ranked shaped r n.
            ShapeInt n -> InputId ranked -> DeltaR ranked shaped r n
  ScaleR :: ranked r n -> DeltaR ranked shaped r n -> DeltaR ranked shaped r n
  AddR :: DeltaR ranked shaped r n -> DeltaR ranked shaped r n
       -> DeltaR ranked shaped r n
  LetR :: NodeId ranked -> DeltaR ranked shaped r n
       -> DeltaR ranked shaped r n

  IndexR :: (KnownNat n, KnownNat m)
         => DeltaR ranked shaped r (m + n) -> IndexOf ranked m
         -> DeltaR ranked shaped r n
    -- ^ The sub-tensor at the given index. The given shape is of the
    -- large tensor. If index is out of bounds, the result is defined and is 0.
  SumR :: KnownNat n
       => DeltaR ranked shaped r (1 + n) -> DeltaR ranked shaped r n
  Sum0R :: KnownNat n
        => DeltaR ranked shaped r n -> DeltaR ranked shaped r 0
  Dot0R :: KnownNat n
        => ranked r n -> DeltaR ranked shaped r n -> DeltaR ranked shaped r 0
  ScatterR :: (KnownNat m, KnownNat p, KnownNat n)
           => ShapeInt (p + n) -> DeltaR ranked shaped r (m + n)
           -> (IndexOf ranked m -> IndexOf ranked p)
           -> DeltaR ranked shaped r (p + n)
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
            => [DeltaR ranked shaped r n] -> DeltaR ranked shaped r (1 + n)
    -- ^ Create a tensor from a list treated as the outermost dimension.
  FromVectorR :: KnownNat n
              => Data.Vector.Vector (DeltaR ranked shaped r n)
              -> DeltaR ranked shaped r (1 + n)
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  ReplicateR :: KnownNat n
             => Int -> DeltaR ranked shaped r n
             -> DeltaR ranked shaped r (1 + n)
    -- ^ Copy the given tensor along the new, outermost dimension.
  AppendR :: KnownNat n
          => DeltaR ranked shaped r (1 + n)
          -> DeltaR ranked shaped r (1 + n)
          -> DeltaR ranked shaped r (1 + n)
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
  SliceR :: KnownNat n
         => Int -> Int -> DeltaR ranked shaped r (1 + n)
         -> DeltaR ranked shaped r (1 + n)
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
  ReverseR :: KnownNat n
           => DeltaR ranked shaped r (1 + n) -> DeltaR ranked shaped r (1 + n)
    -- ^ Reverse elements of the outermost dimension.
  TransposeR :: KnownNat n
             => Permutation -> DeltaR ranked shaped r n
             -> DeltaR ranked shaped r n
    -- ^ Transpose according to the permutation.
  ReshapeR :: (KnownNat n, KnownNat m)
           => ShapeInt m -> DeltaR ranked shaped r n
           -> DeltaR ranked shaped r m
    -- ^ Change the shape of the tensor to the given one.
  BuildR :: KnownNat n
         => Int -> (IntOf ranked -> DeltaR ranked shaped r n)
         -> DeltaR ranked shaped r (1 + n)
    -- ^ Build a tensor with the given size of the outermost dimension
    -- and using the given function to construct the element tensors.
  GatherR :: (KnownNat m, KnownNat p, KnownNat n)
          => ShapeInt (m + n) -> DeltaR ranked shaped r (p + n)
          -> (IndexOf ranked m -> IndexOf ranked p)
          -> DeltaR ranked shaped r (m + n)
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @Gather1 (const Z) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @GatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for Gather1; fix.
  CastR :: (GoodScalar r1, RealFrac r1, RealFrac r2)
        => DeltaR ranked shaped r1 n -> DeltaR ranked shaped r2 n

  DToR :: forall n r ranked shaped.
          DeltaD ranked shaped r '()
       -> DeltaR ranked shaped r n
  SToR :: forall sh r ranked shaped. OS.Shape sh
       => DeltaS ranked shaped r sh
       -> DeltaR ranked shaped r (OS.Rank sh)

deriving instance ( GoodScalar r0
                  , (forall n r. GoodScalar r => Show (ranked r n))
                  , (forall sh r. (OS.Shape sh, GoodScalar r)
                                  => Show (shaped r sh))
                  , Show (IntOf ranked)
                  , Show (IntOf shaped) )
                  => Show (DeltaR ranked shaped r0 n0)

-- | This is the grammar of delta-expressions that record derivatives
-- of shaped tensors.
data DeltaS :: RankedTensorKind -> ShapedTensorKind -> ShapedTensorKind where
  ZeroS :: DeltaS ranked shaped r sh
  InputS :: InputId ranked -> DeltaS ranked shaped r sh
  ScaleS :: shaped r sh -> DeltaS ranked shaped r sh
         -> DeltaS ranked shaped r sh
  AddS :: DeltaS ranked shaped r sh -> DeltaS ranked shaped r sh
       -> DeltaS ranked shaped r sh
  LetS :: NodeId ranked -> DeltaS ranked shaped r sh
       -> DeltaS ranked shaped r sh

  IndexS :: (OS.Shape sh1, OS.Shape (sh1 OS.++ sh2))
         => DeltaS ranked shaped r (sh1 OS.++ sh2)
         -> IndexSh shaped sh1
         -> DeltaS ranked shaped r sh2
    -- ^ The sub-tensor at the given index.
    -- If index is out of bounds, the result is defined and is 0.
  SumS :: KnownNat n
       => DeltaS ranked shaped r (n ': sh) -> DeltaS ranked shaped r sh
  Sum0S :: (OS.Shape sh, KnownNat (OS.Size sh))
        => DeltaS ranked shaped r sh -> DeltaS ranked shaped r '[]
  Dot0S :: (OS.Shape sh, KnownNat (OS.Size sh))
        => shaped r sh -> DeltaS ranked shaped r sh
        -> DeltaS ranked shaped r '[]
  ScatterS :: forall ranked shaped r sh2 p sh.
              ( OS.Shape sh2, OS.Shape (OS.Take p sh), OS.Shape (OS.Drop p sh)
              , OS.Shape (sh2 OS.++ OS.Drop p sh) )
           => DeltaS ranked shaped r (sh2 OS.++ OS.Drop p sh)
           -> (IndexSh shaped sh2
               -> IndexSh shaped (OS.Take p sh))
           -> DeltaS ranked shaped r sh
    -- ^ Build a tensor by adding up tensors of rank @n@ taken from
    -- the third argument and inserted in a zero tensor
    -- at indexes of length @p@. Indexes of length 0 insert tensors trivially,
    -- so that, e.g, @Scatter1 5 (const Z) (Replicate0R [5] d) []@ is equivalent
    -- to @5 * d@. If an index of length @p@ is out of bounds, no tensor
    -- is added at such an index (and similarly in @ScatterN@).
    -- The semantics of the operation permits index out of bounds
    -- and then no tensors is added at such an index.
    -- TODO: this is a haddock for Scatter1; fix.

  FromListS :: (OS.Shape sh, KnownNat n)
            => [DeltaS ranked shaped r sh] -> DeltaS ranked shaped r (n ': sh)
    -- ^ Create a tensor from a list treated as the outermost dimension.
  FromVectorS :: (OS.Shape sh, KnownNat n)
              => Data.Vector.Vector (DeltaS ranked shaped r sh)
              -> DeltaS ranked shaped r (n ': sh)
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  ReplicateS :: forall ranked shaped r n sh.
                (OS.Shape sh, KnownNat n)
             => DeltaS ranked shaped r sh -> DeltaS ranked shaped r (n ': sh)
    -- ^ Copy the given tensor along the new, outermost dimension.
  AppendS :: forall ranked shaped r m n sh.
             (KnownNat m, KnownNat n, OS.Shape sh)
          => DeltaS ranked shaped r (m ': sh)
          -> DeltaS ranked shaped r (n ': sh)
          -> DeltaS ranked shaped r ((m + n) ': sh)
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
    -- The integer argument is the outermost size of the first array.
  SliceS :: forall ranked shaped i n k r sh.
            (KnownNat i, KnownNat n, KnownNat k, OS.Shape sh)
         => DeltaS ranked shaped r (i + n + k ': sh)
         -> DeltaS ranked shaped r (n ': sh)
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
    -- The last argument is the outermost size of the argument array.
  ReverseS :: (OS.Shape sh, KnownNat n)
           => DeltaS ranked shaped r (n ': sh)
           -> DeltaS ranked shaped r (n ': sh)
    -- ^ Reverse elements of the outermost dimension.
  TransposeS :: forall ranked shaped perm r sh.
                ( OS.Permutation perm, OS.Shape perm, OS.Shape sh
                , KnownNat (OS.Rank sh), OS.Rank perm <= OS.Rank sh )
             => DeltaS ranked shaped r sh
             -> DeltaS ranked shaped r (OS.Permute perm sh)
    -- ^ Transpose according to the permutation.
  ReshapeS :: (OS.Shape sh, OS.Size sh ~ OS.Size sh2)
           => DeltaS ranked shaped r sh
           -> DeltaS ranked shaped r sh2
    -- ^ Change the shape of the tensor from the first to the second.
  BuildS :: forall ranked shaped r n sh.
            (OS.Shape sh, KnownNat n)
         => (IntSh shaped n -> DeltaS ranked shaped r sh)
         -> DeltaS ranked shaped r (n ': sh)
    -- ^ Build a tensor with the given size of the outermost dimension
    -- and using the given function to construct the element tensors.
  GatherS :: forall ranked shaped r sh2 p sh.
             ( OS.Shape sh2, OS.Shape sh
             , OS.Shape (OS.Take p sh), OS.Shape (OS.Drop p sh) )
          => DeltaS ranked shaped r sh
          -> (IndexSh shaped sh2
              -> IndexSh shaped (OS.Take p sh))
          -> DeltaS ranked shaped r (sh2 OS.++ OS.Drop p sh)
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @Gather1 (const Z) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @GatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for Gather1; fix.
  CastS :: (GoodScalar r1, RealFrac r1, RealFrac r2)
        => DeltaS ranked shaped r1 sh -> DeltaS ranked shaped r2 sh

  DToS :: forall sh r ranked shaped.
          DeltaD ranked shaped r '()
       -> DeltaS ranked shaped r sh
  RToS :: forall sh r ranked shaped. KnownNat (OS.Rank sh)
       => DeltaR ranked shaped r (OS.Rank sh)
       -> DeltaS ranked shaped r sh

deriving instance ( OS.Shape sh0, GoodScalar r0
                  , (forall n r. GoodScalar r => Show (ranked r n))
                  , (forall sh r. (OS.Shape sh, GoodScalar r)
                                  => Show (shaped r sh))
                  , Show (IntOf ranked)
                  , Show (IntOf shaped) )
                  => Show (DeltaS ranked shaped r0 sh0)

data DeltaD :: RankedTensorKind -> ShapedTensorKind
            -> TensorKind () where
  RToD :: forall n r ranked shaped. KnownNat n
       => DeltaR ranked shaped r n -> DeltaD ranked shaped r '()
  SToD :: forall sh r ranked shaped. OS.Shape sh
       => DeltaS ranked shaped r sh -> DeltaD ranked shaped r '()

deriving instance ( GoodScalar r0
                  , (forall n r. GoodScalar r => Show (ranked r n))
                  , (forall sh r. (OS.Shape sh, GoodScalar r)
                                  => Show (shaped r sh))
                  , Show (IntOf ranked)
                  , Show (IntOf shaped) )
                  => Show (DeltaD ranked shaped r0 '())

shapeDelta :: forall ranked shaped r n. (KnownNat n, RankedTensor ranked)
           => DeltaR ranked shaped r n -> ShapeInt n
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
  BuildR n f -> n :$ shapeDelta (f 0)  -- fishy, but should not appear anyway
  GatherR sh _ _ -> sh
  CastR d -> shapeDelta d
  DToR (RToD @n2 d) ->
    case sameNat (Proxy @n) (Proxy @n2) of
      Just Refl -> shapeDelta d
      _ -> error "shapeDelta: different ranks in DToR(RToD)"
  DToR (SToD @sh _) -> listShapeToShape $ OS.shapeT @sh
  SToR @sh _ -> listShapeToShape $ OS.shapeT @sh

lengthDelta :: forall ranked shaped r n. (KnownNat n, RankedTensor ranked)
            => DeltaR ranked shaped r (1 + n) -> Int
lengthDelta d = case shapeDelta d of
  ZS -> error "lengthDelta: impossible pattern needlessly required"
  k :$ _ -> k


-- * Delta expression identifiers

newtype NodeId (f :: TensorKind k) = NodeId Int
 deriving newtype (Show, Enum)
   -- No Eq instance to limit hacks.

newtype InputId (f :: TensorKind k) = InputId Int
 deriving (Show, Enum)
   -- No Eq instance to limit hacks outside this module.

-- | Wrap non-negative (only!) integers in the `InputId` newtype.
toInputId :: Int -> InputId f
toInputId i = assert (i >= 0) $ InputId i


-- * Evaluation of the delta expressions

type DualPart :: TensorKind k -> Constraint
class DualPart (f :: TensorKind k) where
  -- | The type family that to each basic differentiable type
  -- assigns its delta expression type.
  type Dual f = (result :: TensorKind k) | result -> f
  reverseDervative
    :: (HasSingletonDict y, GoodScalar r)
    => Int -> f r y -> Maybe (f r y) -> Dual f r y
    -> (AstBindings f, Domains (DynamicOf f))
  forwardDerivative
    :: (HasSingletonDict y, GoodScalar r)
    => Int -> Dual f r y -> Domains (DynamicOf f)
    -> (AstBindings f, f r y)

instance DualPart @() (Clown OD.Array) where
  type Dual (Clown OD.Array) = DeltaD (Flip OR.Array) (Flip OS.Array)
  reverseDervative = gradientDtD
  forwardDerivative = derivativeFromDeltaD

instance DualPart @() (Clown (AstDynamic PrimalSpan)) where
  type Dual (Clown (AstDynamic PrimalSpan)) =
    DeltaD (AstRanked PrimalSpan) (AstShaped PrimalSpan)
  reverseDervative = gradientDtD
  forwardDerivative = derivativeFromDeltaD

gradientDtD
  :: forall ranked shaped r (y :: ()).
     ( GoodScalar r
     , RankedTensor ranked, ShapedTensor shaped, ConvertTensor ranked shaped )
  => Int -> Clown (DynamicOf ranked) r y
  -> Maybe (Clown (DynamicOf ranked) r y)
  -> DeltaD ranked shaped r y
  -> ( AstBindings ranked
     , Domains (DynamicOf ranked) )
gradientDtD !dims !value !mdt !deltaTopLevel =
  let shl = dshape @ranked (runClown value)
      n = length shl
  in case someNatVal $ toInteger n of
    Just (SomeNat @n _proxy) ->
      let sh = listShapeToShape @n shl
          dt = maybe (dfromR @ranked $ treplicate0N sh 1) runClown mdt
          deltaDt = DeltaDtD dt deltaTopLevel
      in gradientFromDelta dims deltaDt
    Nothing -> error "gradientDtD: impossible someNatVal error"

derivativeFromDeltaD
  :: forall ranked shaped r (y :: ()).
     ( GoodScalar r
     , RankedTensor ranked, ShapedTensor shaped, ConvertTensor ranked shaped )
  => Int -> DeltaD ranked shaped r y -> Domains (DynamicOf ranked)
  -> ( AstBindings ranked
     , Clown (DynamicOf ranked) r y )
derivativeFromDeltaD !dim !deltaTopLevel !ds =
  case runST $ buildDerivative dim (DeltaDtD (dfromR @ranked @shaped @r @0 0)
                                             deltaTopLevel) ds of
    (l, DeltaDtD res _) -> (l, Clown res)
    (_, DeltaDtR{}) -> error "derivativeFromDeltaD"
    (_, DeltaDtS{}) -> error "derivativeFromDeltaD"

instance DualPart @Nat (Flip OR.Array) where
  type Dual (Flip OR.Array) = DeltaR (Flip OR.Array) (Flip OS.Array)
  reverseDervative = gradientDtR
  forwardDerivative = derivativeFromDeltaR

instance DualPart @Nat (AstRanked PrimalSpan) where
  type Dual (AstRanked PrimalSpan) =
    DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan)
  reverseDervative = gradientDtR
  forwardDerivative = derivativeFromDeltaR

gradientDtR
  :: ( KnownNat y, GoodScalar r
     , RankedTensor ranked, ShapedTensor shaped, ConvertTensor ranked shaped )
  => Int -> ranked r y -> Maybe (ranked r y)
  -> DeltaR ranked shaped r y
  -> ( AstBindings ranked
     , Domains (DynamicOf ranked) )
gradientDtR !dims value !mdt !deltaTopLevel =
  let dt = fromMaybe (treplicate0N (tshape value) 1) mdt
      deltaDt = DeltaDtR dt deltaTopLevel
  in gradientFromDelta dims deltaDt
{-# SPECIALIZE gradientDtR
  :: KnownNat y
  => Int -> Flip OR.Array Double y -> Maybe (Flip OR.Array Double y)
  -> DeltaR (Flip OR.Array) (Flip OS.Array) Double y
  -> ( AstBindings (Flip OR.Array)
     , Domains (DynamicOf (Flip OR.Array)) ) #-}
{-# SPECIALIZE gradientDtR
  :: KnownNat y
  => Int -> AstRanked PrimalSpan Double y
  -> Maybe (AstRanked PrimalSpan Double y)
  -> DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan) Double y
  -> ( AstBindings (AstRanked PrimalSpan)
     , Domains (DynamicOf (AstRanked PrimalSpan)) ) #-}

derivativeFromDeltaR
  :: forall ranked shaped r n.
       ( KnownNat n, GoodScalar r
       , RankedTensor ranked, ShapedTensor shaped, ConvertTensor ranked shaped )
  => Int -> DeltaR ranked shaped r n -> Domains (DynamicOf ranked)
  -> ( AstBindings ranked
     , ranked r n )
derivativeFromDeltaR dim deltaTopLevel ds =
  let dummyZero = tzero $ listShapeToShape $ replicate (valueOf @n) 1
  in case runST $ buildDerivative dim (DeltaDtR dummyZero deltaTopLevel) ds of
    (l, DeltaDtR @_ @n2 res _) -> case sameNat (Proxy @n) (Proxy @n2) of
      Just Refl -> (l, res)
      _ -> error "derivativeFromDeltaR"
    (_, DeltaDtS{}) -> error "derivativeFromDeltaR"
    (_, DeltaDtD{}) -> error "derivativeFromDeltaR"

instance DualPart @[Nat] (Flip OS.Array) where
  type Dual (Flip OS.Array) = DeltaS (Flip OR.Array) (Flip OS.Array)
  reverseDervative dims _ = gradientDtS dims
  forwardDerivative = derivativeFromDeltaS

instance DualPart @[Nat] (AstShaped PrimalSpan) where
  type Dual (AstShaped PrimalSpan) =
    DeltaS (AstRanked PrimalSpan) (AstShaped PrimalSpan)
  reverseDervative dims _ = gradientDtS dims
  forwardDerivative = derivativeFromDeltaS

gradientDtS
  :: forall ranked shaped r y.
     ( OS.Shape y, GoodScalar r
     , RankedTensor ranked, ShapedTensor shaped, ConvertTensor ranked shaped )
  => Int -> Maybe (shaped r y) -> DeltaS ranked shaped r y
  -> ( AstBindings ranked
     , Domains (DynamicOf shaped) )
gradientDtS !dims !mdt !deltaTopLevel =
  let dt = fromMaybe 1 mdt
      deltaDt = DeltaDtS dt deltaTopLevel
  in gradientFromDelta dims deltaDt
{-# SPECIALIZE gradientDtS
  :: OS.Shape y
  => Int -> Maybe (Flip OS.Array Double y)
  -> DeltaS (Flip OR.Array) (Flip OS.Array) Double y
  -> ( AstBindings (Flip OS.Array)
     , Domains (DynamicOf (Flip OS.Array)) ) #-}
{-# SPECIALIZE gradientDtS
  :: OS.Shape y
  => Int -> Maybe (AstShaped PrimalSpan Double y)
  -> DeltaS (AstRanked PrimalSpan) (AstShaped PrimalSpan) Double y
  -> ( AstBindings (AstShaped PrimalSpan)
     , Domains (DynamicOf (AstShaped PrimalSpan)) ) #-}

derivativeFromDeltaS
  :: forall ranked shaped r sh.
     ( OS.Shape sh, GoodScalar r
     , RankedTensor ranked, ShapedTensor shaped, ConvertTensor ranked shaped )
  => Int -> DeltaS ranked shaped r sh -> Domains (DynamicOf shaped)
  -> ( AstBindings ranked
     , shaped r sh )
derivativeFromDeltaS !dim !deltaTopLevel !ds =
  case runST $ buildDerivative dim (DeltaDtS 0 deltaTopLevel) ds of
    (l, DeltaDtS @_ @sh2 res _) -> case sameShape @sh @sh2 of
      Just Refl -> (l, res)
      _ -> error "derivativeFromDeltaS"
    (_, DeltaDtR{}) -> error "derivativeFromDeltaS"
    (_, DeltaDtD{}) -> error "derivativeFromDeltaS"

-- | The main input of the differentiation functions:
-- the delta expression to be differentiated and the dt perturbation
-- (small change) of the objective function codomain, for which we compute
-- the gradient.
data DeltaDt :: RankedTensorKind -> ShapedTensorKind -> Type -> Type where
  DeltaDtR :: forall r n ranked shaped. KnownNat n
           => ranked r n -> DeltaR ranked shaped r n
           -> DeltaDt ranked shaped r
  DeltaDtS :: forall r sh ranked shaped. OS.Shape sh
           => shaped r sh -> DeltaS ranked shaped r sh
           -> DeltaDt ranked shaped r
  DeltaDtD :: forall r (y :: ()) ranked shaped.
              DynamicOf ranked r -> DeltaD ranked shaped r y
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
data EvalState ranked shaped = EvalState
  { iMap        :: EM.EnumMap (InputId ranked)
                              (DynamicExists (DynamicOf ranked))
      -- ^ eventually, cotangents of objective function inputs
      -- (eventually copied to the vector representing the gradient
      -- of the objective function);
      -- the identifiers need to be contiguous and start at 0
  , dMap        :: EM.EnumMap (NodeId ranked) (DynamicExists (DynamicOf ranked))
      -- ^ eventually, cotangents of non-input subterms indexed
      -- by their node identifiers
  , nMap        :: EM.EnumMap (NodeId ranked) (DeltaBinding ranked shaped)
      -- ^ nodes left to be evaluated
  , astBindings :: AstBindings ranked
  }

-- | Nodes left to be evaluated.
-- We can't evaluate them at once, because their other shared copies
-- may still not be processed, so we'd not take advantage of the sharing
-- and not take into account the whole summed context when finally evaluating.
data DeltaBinding :: RankedTensorKind -> ShapedTensorKind -> Type where
  DeltaBindingR :: forall n r ranked shaped. (KnownNat n, GoodScalar r)
                => DeltaR ranked shaped r n -> DeltaBinding ranked shaped
  DeltaBindingS :: forall sh r ranked shaped. (OS.Shape sh, GoodScalar r)
                => DeltaS ranked shaped r sh -> DeltaBinding ranked shaped

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
      , ConvertTensor ranked shaped )
  => Int -> DeltaDt ranked shaped r
  -> ( AstBindings ranked
     , Domains (DynamicOf ranked) )
gradientFromDelta !dims !deltaDt =
  -- Create finite maps that hold values associated with inputs
  -- and with (possibly shared) term tree nodes.
  -- The former are initialized with dummy values so that it's cheap
  -- to check if any update has already been performed to a cell
  -- (allocating big vectors filled with zeros is too costly,
  -- especially if never used in an iteration, and adding to such vectors
  -- and especially using them as cotangent accumulators is wasteful;
  -- additionally, it may not be easy to deduce the sizes of the vectors).
  let s0 =
        let dummy = ddummy @ranked @shaped @CInt  -- any GoodScalar is fine
            iMap = EM.fromDistinctAscList
                   $ zip [toInputId 0 ..] (replicate dims (DynamicExists dummy))
            dMap = EM.empty
            nMap = EM.empty
            astBindings = []
        in EvalState {..}
  in let -- Eval.
         EvalState{..} = buildFinMaps s0 deltaDt
         -- Extract results.
         !gradient = V.fromList $ EM.elems iMap
     in (astBindings, gradient)
{- TODO: no type application possible, so a (buggy?) warning is shown
{-# SPECIALIZE gradientFromDelta
  :: Int -> DeltaDt (Flip OR.Array) (Flip OS.Array) Double
  -> (AstBindings (Clown OD.Array), DomainsOD) #-}
-}
{-# SPECIALIZE gradientFromDelta
  :: Int -> DeltaDt (AstRanked PrimalSpan) (AstShaped PrimalSpan) Double
  -> (AstBindings (AstRanked PrimalSpan), Domains (AstDynamic PrimalSpan)) #-}

buildFinMaps
  :: forall ranked shaped r0.
     ( GoodScalar r0, RankedTensor ranked, ShapedTensor shaped
     , ConvertTensor ranked shaped )
  => EvalState ranked shaped -> DeltaDt ranked shaped r0
  -> EvalState ranked shaped
buildFinMaps s0 deltaDt =
  -- The first argument is the evaluation state being modified,
  -- the second is the cotangent accumulator that will become an actual
  -- cotangent contribution when complete (see below for an explanation)
  -- and the third argument is the node to evaluate.
  let evalR :: forall n r. (KnownNat n, GoodScalar r)
            => EvalState ranked shaped
            -> ranked r n -> DeltaR ranked shaped r n
            -> EvalState ranked shaped
      evalR !s !c = let (abShared, cShared) = tregister c (astBindings s)
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
                    DToR{} -> False
                    LetR{} -> False  -- wasteful and nonsensical
                    _ -> True)
          $ case EM.lookup n $ nMap s of
              Just (DeltaBindingR _) ->
                s {dMap = EM.adjust (raddDynamic c) n $ dMap s}
              Nothing ->
                let cs = DynamicExists $ dfromR c
                in s { nMap = EM.insert n (DeltaBindingR d) $ nMap s
                     , dMap = EM.insert n cs $ dMap s }
              _ -> error "buildFinMaps: corrupted nMap"

        IndexR d ix -> evalR s (tscatter @ranked @r @0
                                             (shapeDelta d) c (const ix)) d
          -- equivalent: evalR s (updateNR (treplicate0NR sh 0) [(ix, c)]) d
        SumR d -> evalR s (treplicate (lengthDelta d) c) d
        Sum0R d -> evalR s (treplicate0N (shapeDelta d) c) d
        Dot0R v vd -> evalR s (v * treplicate0N (tshape v) c) vd
                     -- too slow: evalR s (tmap0N (* (tscalar c)) v) vd
        ScatterR _sh d f -> evalR s (tgather (shapeDelta d) c f) d

        FromListR ld ->
          ifoldl' (\s2 i d2 ->
            evalR s2 (tindex cShared (fromIntegral i :. ZI)) d2) sShared ld
        FromVectorR ld ->
          V.ifoldl' (\s2 i d2 ->
            evalR s2 (tindex cShared (fromIntegral i :. ZI)) d2) sShared ld
        ReplicateR _n d -> evalR s (tsum c) d
        AppendR d e -> case tshape c of
          n :$ _ -> let k = lengthDelta d
                        s2 = evalR sShared (tslice 0 k cShared) d
                    in evalR s2 (tslice k (n - k) cShared) e
          ZS -> error "evalR: impossible pattern needlessly required"
        SliceR i n d -> case tshape c of
          n' :$ rest ->
            assert (n' == n `blame` (n', n)) $
            evalR s (tconcat [ tzero (i :$ rest)
                             , c
                             , tzero (lengthDelta d - i - n :$ rest) ])
                    d
          ZS -> error "evalR: impossible pattern needlessly required"
        ReverseR d -> evalR s (treverse c) d
        TransposeR perm d ->
          let perm_reversed = map snd $ sort $ zip perm [0 .. length perm - 1]
          in evalR s (ttranspose perm_reversed c) d
        ReshapeR _sh d -> evalR s (treshape (shapeDelta d) c) d
        BuildR n f ->
          foldl' (\s2 i -> evalR s2 (tindex cShared (i :. ZI)) (f i))
                 sShared (fromIntegral <$> [0 .. n - 1])
        GatherR _sh d f -> evalR s (tscatter (shapeDelta d) c f) d
        CastR d -> evalR s (tcast c) d

        DToR (RToD @n2 d) ->
          case sameNat (Proxy @n) (Proxy @n2) of
            Just Refl -> evalR s c d
            _ -> error "buildFinMaps: different ranks in DToR(RToD)"
        DToR (SToD @sh2 d) ->
          case matchingRank @sh2 @n of
            Just Refl -> evalR s c (SToR d)
            _ -> error "buildFinMaps: different ranks in DToR(SToD)"
        SToR (RToS d) -> evalR s c d  -- no information lost, so no checks
        SToR d -> evalS s (sfromR c) d

      evalS :: forall sh r. (OS.Shape sh, GoodScalar r)
            => EvalState ranked shaped
            -> shaped r sh -> DeltaS ranked shaped r sh
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
                    DToS{} -> False
                    LetS{} -> False  -- wasteful and nonsensical
                    _ -> True)
          $ case EM.lookup n $ nMap s of
              Just (DeltaBindingS _) ->
                s {dMap = EM.adjust (saddDynamic c) n $ dMap s}
              Nothing ->
                let cs = DynamicExists $ dfromS c
                in s { nMap = EM.insert n (DeltaBindingS d) $ nMap s
                     , dMap = EM.insert n cs $ dMap s }
              _ -> error "buildFinMaps: corrupted nMap"

        IndexS @sh1 d ix ->
          gcastWith (unsafeCoerce Refl
                     :: OS.Drop (OS.Rank sh1) (sh1 OS.++ sh) :~: sh)
          $ gcastWith (unsafeCoerce Refl
                       :: OS.Take (OS.Rank sh1) (sh1 OS.++ sh) :~: sh1)
          $ evalS s (sscatter @shaped @r @'[] @(OS.Rank sh1) c (const ix)) d
          -- equivalent: evalS s (updateNR (replicate0NR sh 0) [(ix, c)]) d
        SumS d -> evalS s (sreplicate c) d
        Sum0S d -> evalS s (sreplicate0N c) d
        Dot0S v vd -> evalS s (v * sreplicate0N c) vd
          -- too slow: evalS s (smap0N (* (sscalar c)) v) vd
        ScatterS d f -> evalS s (sgather c f) d

        FromListS ld ->
          ifoldl' (\s2 i d2 ->
            evalS s2 (cShared !$ (fromIntegral i :$: ZSH)) d2) sShared ld
        FromVectorS ld ->
          V.ifoldl' (\s2 i d2 ->
            evalS s2 (cShared !$ (fromIntegral i :$: ZSH)) d2) sShared ld
        ReplicateS d -> evalS s (ssum c) d
        AppendS @_ @_ @_ @m @n d e ->
          let s2 = evalS sShared (sslice (Proxy @0) Proxy cShared) d
          in evalS s2 (sslice (Proxy @m) Proxy cShared) e
        SliceS @_ @_ @i d ->
          evalS s (sappend @shaped @r @i 0 (sappend c 0)) d
        ReverseS d -> evalS s (sreverse c) d
        TransposeS @_ @_ @perm @_ @sh2 d ->
          -- Reversing the permutation at the type level would be too hard,
          -- so we unsafeCoerce, knowing that it's safe in this case.
          -- TODO: instead add a tensor operation that permutes
          -- in the other direction? What if backend don't have it?
          let perm = OS.shapeT @perm
              permRev = map snd $ sort $ zip perm [0 .. length perm - 1]
          in OS.withShapeP permRev $ \(_proxy :: Proxy permRev) ->
            gcastWith (unsafeCoerce Refl
                       :: OS.Permute permRev sh :~: sh2)
            $ gcastWith (unsafeCoerce Refl
                         :: OS.Rank sh :~: OS.Rank sh2)
            $ gcastWith (unsafeCoerce Refl
                         :: OS.Rank permRev :~: OS.Rank perm)
            $ evalS s
                    (trustMeThisIsAPermutation @permRev
                       (stranspose (Proxy @permRev))
                       c)
                    d
        ReshapeS d -> evalS s (sreshape c) d
        BuildS @_ @_ @_ @n f ->
          foldl' (\s2 i -> evalS s2 (sindex cShared (i :$: ZSH))
                                 (f $ ShapedList.shapedNat i))
                 sShared (fromIntegral <$> [0 .. (valueOf @n :: Int) - 1])
        GatherS d f -> evalS s (sscatter c f) d
        CastS d -> evalS s (scast c) d

        DToS (SToD @sh2 d) ->
          case sameShape @sh @sh2 of
            Just Refl -> evalS s c d
            _ -> error "buildFinMaps: different shapes in DToS(SToD)"
        DToS (RToD @n2 d) ->
          case matchingRank @sh @n2 of
            Just Refl -> evalS s c (RToS d)
            _ -> error "buildFinMaps: different ranks in DToS(RToD)"
        RToS (SToR @sh2 d) ->
          case sameShape @sh @sh2 of
            Just Refl -> evalS s c d
            _ -> error "buildFinMaps: different shapes in RToS(SToR)"
        RToS d -> evalR s (tfromS c) d

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
                    else v `OD.update` [(ixs, v `tindex0D` ixs + c)]
          in s {iMap = EM.adjust f i $ iMap s}
        Index0 (LetR n d) ixs' sh ->
          let ixs = indexToList ixs'
          in case EM.lookup n $ nMap s of
            Just (DeltaBindingR _) ->
              let f v = v `OD.update` [(ixs, v `tindex0D` ixs + c)]
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

      evalD :: GoodScalar r
            => EvalState ranked shaped
            -> DynamicOf ranked r -> DeltaD ranked shaped r y
            -> EvalState ranked shaped
      evalD s !c = \case
        RToD d -> evalR s (tfromD c) d
        SToD d -> evalS s (sfromD c) d

      evalFromnMap :: EvalState ranked shaped -> EvalState ranked shaped
      evalFromnMap s@EvalState{nMap, dMap} =
        case EM.maxViewWithKey nMap of
          Just ((n, b), nMap2) ->
            let s2 = s {nMap = nMap2}
                s3 = case b of
                  DeltaBindingS @_ @r1 d -> case dMap EM.! n of
                    DynamicExists @r2 e ->
                      case testEquality (typeRep @r1) (typeRep @r2) of
                        Just Refl -> let c = sfromD e
                                     in evalS s2 c d
                        _ -> error "buildFinMaps: type mismatch"
                  DeltaBindingR @_ @r1 d -> case dMap EM.! n of
                    DynamicExists @r2 e ->
                      case testEquality (typeRep @r1) (typeRep @r2) of
                        Just Refl -> let c = tfromD e
                                     in evalR s2 c d
                        _ -> error "buildFinMaps: type mismatch"
            in evalFromnMap s3
          Nothing -> s  -- loop ends

      s1 = case deltaDt of
        DeltaDtS dt deltaTopLevel -> evalS s0 dt deltaTopLevel
        DeltaDtR dt deltaTopLevel -> evalR s0 dt deltaTopLevel
        DeltaDtD dt deltaTopLevel -> evalD s0 dt deltaTopLevel
  in evalFromnMap s1
{-# SPECIALIZE buildFinMaps
  :: EvalState (Flip OR.Array) (Flip OS.Array) -> DeltaDt (Flip OR.Array) (Flip OS.Array) Double -> EvalState (Flip OR.Array) (Flip OS.Array) #-}
{-# SPECIALIZE buildFinMaps
  :: EvalState (AstRanked PrimalSpan) (AstShaped PrimalSpan) -> DeltaDt (AstRanked PrimalSpan) (AstShaped PrimalSpan) Double -> EvalState (AstRanked PrimalSpan) (AstShaped PrimalSpan) #-}


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
     , ConvertTensor ranked shaped )
  => Int -> DeltaDt ranked shaped r0 -> Domains (DynamicOf ranked)
  -> ST s ( AstBindings ranked
          , DeltaDt ranked shaped r0 )
buildDerivative dimR deltaDt params = do
  dMap <- newSTRef EM.empty
  nMap <- newSTRef EM.empty
  astBindings <- newSTRef []
  let evalR :: forall n r. (KnownNat n, GoodScalar r)
            => DeltaR ranked shaped r n -> ST s (ranked r n)
      evalR = \case
        ZeroR sh -> return $ tzero sh
        InputR _ (InputId i) ->
          if i < dimR
          then case params V.! i of
            DynamicExists @r2 e ->
              case testEquality (typeRep @r) (typeRep @r2) of
                Just Refl -> return $! tfromD e
                _ -> error "buildDerivative: type mismatch"
          else error "buildDerivative': wrong index for an input"
        ScaleR k d -> (* k) <$> evalR d
        AddR d e -> liftM2 (+) (evalR d) (evalR e)
        LetR n d -> do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBindingR _) -> do
              dm <- readSTRef dMap
              case dm EM.! n of
                DynamicExists @r2 t ->
                  case testEquality (typeRep @r) (typeRep @r2) of
                    Just Refl -> return $! tfromD t
                    _ -> error "buildDerivative: type mismatch"
            Nothing -> do
              cRaw <- evalR d
              ab <- readSTRef astBindings
              let (abShared, cShared) = tregister cRaw ab
              writeSTRef astBindings abShared
              nmNew <- readSTRef nMap
              writeSTRef nMap $! EM.insert n (DeltaBindingR d) nmNew
              dm <- readSTRef dMap
              writeSTRef dMap $! EM.insert n (DynamicExists $ dfromR cShared) dm
              return cShared
            _ -> error "buildDerivative: corrupted nMap"

        IndexR d ix -> (`tindex` ix) <$> evalR d
        SumR d -> tsum <$> evalR d
        Sum0R ZeroR{} -> return 0
        Sum0R d -> tsum0 <$> evalR d
        Dot0R _ ZeroR{} -> return 0
        Dot0R v d -> tdot0 v <$> evalR d
        ScatterR sh d f -> do
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
        AppendR d e -> liftM2 tappend (evalR d) (evalR e)
        SliceR i n d -> tslice i n <$> evalR d
        ReverseR d -> treverse <$> evalR d
        TransposeR perm d -> ttranspose perm <$> evalR d
        ReshapeR sh d -> treshape sh <$> evalR d
        BuildR n f -> do
          l <- mapM (evalR . f . fromIntegral) [0 .. n - 1]
          return $! tfromList l
        GatherR sh d f -> do
          t <- evalR d
          return $! tgather sh t f
        CastR d -> do
          t <- evalR d
          return $! tcast t

        DToR (RToD @n2 d) ->
          case sameNat (Proxy @n) (Proxy @n2) of
            Just Refl -> evalR d
            _ -> error "buildDerivative: different ranks in DToR(RToD)"
        DToR (SToD @sh2 d) ->
          case matchingRank @sh2 @n of
            Just Refl -> evalR (SToR d)
            _ -> error "buildDerivative: different ranks in DToR(SToD)"
        SToR (RToS d) -> evalR d  -- no information lost, so no checks
        SToR d -> tfromS <$> evalS d

      evalS :: forall sh r. (OS.Shape sh, GoodScalar r)
            => DeltaS ranked shaped r sh -> ST s (shaped r sh)
      evalS = \case
        ZeroS -> return 0
        InputS (InputId i) ->
          if i < dimR
          then case params V.! i of
            DynamicExists @r2 e ->
              case testEquality (typeRep @r) (typeRep @r2) of
                Just Refl -> return $! sfromD e
                _ -> error "buildDerivative: type mismatch"
          else error "buildDerivative: wrong index for an input"
        ScaleS k d -> (* k) <$> evalS d
        AddS d e -> liftM2 (+) (evalS d) (evalS e)
        LetS n d -> do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBindingS _) -> do
              dm <- readSTRef dMap
              case dm EM.! n of
                DynamicExists @r2 t ->
                  case testEquality (typeRep @r) (typeRep @r2) of
                    Just Refl -> return $! sfromD t
                    _ -> error "buildDerivative: type mismatch"
            Nothing -> do
              cRaw <- evalS d
              ab <- readSTRef astBindings
              let (abShared, cShared) = sregister cRaw ab
              writeSTRef astBindings abShared
              nmNew <- readSTRef nMap
              writeSTRef nMap $! EM.insert n (DeltaBindingS d) nmNew
              dm <- readSTRef dMap
              writeSTRef dMap $! EM.insert n (DynamicExists $ dfromS cShared) dm
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
        SliceS @_ @_ @i d -> sslice (Proxy @i) Proxy <$> evalS d
        ReverseS d -> sreverse <$> evalS d
        TransposeS @_ @_ @perm d -> stranspose (Proxy @perm) <$> evalS d
        ReshapeS d -> sreshape <$> evalS d
        BuildS @_ @_ @_ @n f -> do
          l <- mapM (evalS . f . ShapedList.shapedNat . fromIntegral)
                    [0 .. (valueOf @n :: Int) - 1]
          return $! sfromList l
        GatherS d f -> do
          t <- evalS d
          return $! sgather t f
        CastS d -> do
          t <- evalS d
          return $! scast t

        DToS (SToD @sh2 d) ->
          case sameShape @sh @sh2 of
            Just Refl -> evalS d
            _ -> error "buildDerivative: different ranks in DToR(RToD)"
        DToS (RToD @n2 d) ->
          case matchingRank @sh @n2 of
            Just Refl -> evalS (RToS d)
            _ -> error "buildDerivative: different ranks in DToR(SToD)"
        RToS (SToR @sh2 d) ->
          case sameShape @sh @sh2 of
            Just Refl -> evalS d
            _ -> error "buildDerivative: different shapes in RToS(SToR)"
        RToS d -> sfromR <$> evalR d

      evalD :: GoodScalar r
            => DeltaD ranked shaped r y -> ST s (DynamicOf ranked r)
      evalD = \case
        RToD d -> dfromR <$> evalR d
        SToD d -> dfromS <$> evalS d

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
    DeltaDtD _dt deltaTopLevel -> do
      c <- evalD deltaTopLevel
      let !cDelta = DeltaDtD c (SToD @'[] ZeroS)
      ab <- readSTRef astBindings
      return (ab, cDelta)
