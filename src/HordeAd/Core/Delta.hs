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
    DeltaR (..), DeltaS (..), DeltaH (..)
  , -- * Delta expression identifiers
    NodeId (..), InputId, toInputId
  , -- * Evaluation of the delta expressions
    DualPart(..)
    -- * Exported to be specialized elsewhere
  , gradientFromDeltaR, gradientFromDeltaS, evalFromnMap, EvalState
  ) where

import Prelude

import           Control.Arrow (second)
import           Control.Exception.Assert.Sugar
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import qualified Data.EnumMap.Strict as EM
import           Data.Int (Int64)
import           Data.Kind (Constraint, Type)
import           Data.List (foldl', sort)
import           Data.List.Index (ifoldl')
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Traversable (mapAccumL)
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.Show (showSpace)
import           GHC.TypeLits (KnownNat, Nat, sameNat, type (+), type (<=))
import           Text.Show.Functions ()
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Ast (ADShare)
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances
  (sameShape, trustMeThisIsAPermutation)
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
    -- ^ the shape is required for @shapeDeltaR@ and forward derivative
  InputR :: forall ranked r n.
            ShapeInt n -> InputId ranked -> DeltaR ranked r n
  ScaleR :: ranked r n -> DeltaR ranked r n -> DeltaR ranked r n
  AddR :: DeltaR ranked r n -> DeltaR ranked r n
       -> DeltaR ranked r n
  LetR :: NodeId ranked -> DeltaR ranked r n -> DeltaR ranked r n

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
  CastR :: (GoodScalar r1, RealFrac r1, RealFrac r2)
        => DeltaR ranked r1 n -> DeltaR ranked r2 n
  RFromS :: forall sh r ranked. Sh.Shape sh
         => DeltaS (ShapedOf ranked) r sh
         -> DeltaR ranked r (Sh.Rank sh)
  RFromH :: DeltaH ranked -> Int -> DeltaR ranked r n

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
  LetS :: NodeId (RankedOf shaped) -> DeltaS shaped r sh -> DeltaS shaped r sh

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
  CastS :: (GoodScalar r1, RealFrac r1, RealFrac r2)
        => DeltaS shaped r1 sh -> DeltaS shaped r2 sh
  SFromR :: forall sh r shaped. KnownNat (Sh.Rank sh)
         => DeltaR (RankedOf shaped) r (Sh.Rank sh)
         -> DeltaS shaped r sh
  SFromH :: DeltaH (RankedOf shaped) -> Int -> DeltaS shaped r sh

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

type role DeltaH nominal
data DeltaH :: RankedTensorType -> Type where
  LetH :: NodeId ranked -> DeltaH ranked -> DeltaH ranked
  HToH :: HVector (DeltaR ranked) -> DeltaH ranked
  MapAccumR
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> HVector ranked
    -> HVector ranked
    -> HFun
    -> HFun
    -> HVector (DeltaR ranked)
    -> HVector (DeltaR ranked)
    -> DeltaH ranked
  MapAccumL
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> HVector ranked
    -> HVector ranked
    -> HFun
    -> HFun
    -> HVector (DeltaR ranked)
    -> HVector (DeltaR ranked)
    -> DeltaH ranked

{- Fails due to @forall f@. Replaced by a manually fixed version at the end
   of this file.
deriving instance ( Show (IntOf ranked)
                  , Show (IntOf (ShapedOf ranked))
                  , CRanked ranked Show
                  , CShaped (ShapedOf ranked) Show
                  , CRanked (DeltaR ranked) Show
                  , CShaped (DeltaS (ShapedOf ranked)) Show )
                  => Show (DeltaH ranked)
-}

-- This is needed for the Show instances due to HVector (Delta...)
-- referring to ShapedOf (Delta..).
type instance RankedOf (DeltaS shaped) = DeltaR (RankedOf shaped)

type instance ShapedOf (DeltaR ranked) = DeltaS (ShapedOf ranked)

type instance HVectorOf (DeltaR ranked) = DeltaH ranked

shapeDeltaR :: forall ranked r n.
               ( GoodScalar r, KnownNat n
               , RankedTensor ranked, ShapedTensor (ShapedOf ranked) )
            => DeltaR ranked r n -> ShapeInt n
shapeDeltaR = \case
  ZeroR sh -> sh
  InputR sh _ -> sh
  ScaleR _ d -> shapeDeltaR d
  AddR d _ -> shapeDeltaR d
  LetR _ d -> shapeDeltaR d
  IndexR d _ -> dropShape (shapeDeltaR d)
  SumR d -> tailShape (shapeDeltaR d)
  Sum0R{} -> ZS
  Dot0R{} -> ZS
  ScatterR sh _ _ -> sh
  FromListR l -> case l of
    [] -> case sameNat (Proxy @n) (Proxy @1) of
      Just Refl -> singletonShape 0  -- the only case where we can guess sh
      _ -> error "shapeDeltaR: FromListR with no arguments"
    d : _ -> length l :$ shapeDeltaR d
  FromVectorR l -> case V.toList l of
    [] -> case sameNat (Proxy @n) (Proxy @1) of
      Just Refl -> singletonShape 0  -- the only case where we can guess sh
      _ -> error "shapeDeltaR: FromListR with no arguments"
    d : _ -> length l :$ shapeDeltaR d
  ReplicateR n d -> n :$ shapeDeltaR d
  AppendR x y -> case shapeDeltaR x of
    ZS -> error "shapeDeltaR: impossible pattern needlessly required"
    xi :$ xsh -> case shapeDeltaR y of
      ZS -> error "shapeDeltaR: impossible pattern needlessly required"
      yi :$ _ -> xi + yi :$ xsh
  SliceR _ n d -> n :$ tailShape (shapeDeltaR d)
  ReverseR d -> shapeDeltaR d
  TransposeR perm d -> backpermutePrefixShape perm (shapeDeltaR d)
  ReshapeR sh _ -> sh
  GatherR sh _ _ -> sh
  CastR d -> shapeDeltaR d
  RFromS @sh _ -> listShapeToShape $ Sh.shapeT @sh
  RFromH d i -> listShapeToShape $ shapeVoidDynamic (shapeDeltaH d V.! i)

lengthDeltaR :: forall ranked r n.
                ( GoodScalar r, KnownNat n
                , RankedTensor ranked, ShapedTensor (ShapedOf ranked) )
             => DeltaR ranked r (1 + n) -> Int
lengthDeltaR d = case shapeDeltaR d of
  ZS -> error "lengthDeltaR: impossible pattern needlessly required"
  k :$ _ -> k

shapeDeltaH :: forall ranked.
               (RankedTensor ranked, ShapedTensor (ShapedOf ranked))
            => DeltaH ranked -> VoidHVector
shapeDeltaH = \case
  LetH _ d -> shapeDeltaH d
  HToH v ->
    V.map (\d -> voidFromDynamicF (shapeToList . shapeDeltaR) d) v
  MapAccumR k accShs bShs _eShs _q _es _df _rf _acc0' _es' ->
    accShs V.++ replicate1VoidHVector k bShs
  MapAccumL k accShs bShs _eShs _q _es _df _rf _acc0' _es' ->
    accShs V.++ replicate1VoidHVector k bShs


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


-- * Instances

type DualPart :: TensorType ty -> Constraint
class DualPart (f :: TensorType ty) where
  -- | The type family that to each basic differentiable type
  -- assigns its delta expression type.
  type Dual f = (result :: TensorType ty) | result -> f
  reverseDervative
    :: (HasSingletonDict y, GoodScalar r)
    => VoidHVector -> f r y -> Maybe (f r y) -> Dual f r y
    -> (AstBindingsD (RankedOf f), HVector (RankedOf f))
  forwardDerivative
    :: (HasSingletonDict y, GoodScalar r)
    => Int -> Dual f r y -> HVector (RankedOf f)
    -> (AstBindingsD (RankedOf f), f r y)
  unlet
    :: (HasSingletonDict y, GoodScalar r)
    => ADShare -> AstBindingsD (RankedOf f) -> f r y -> f r y

instance ADReady ranked => DualPart @Nat ranked where
  type Dual ranked = DeltaR ranked
  reverseDervative = gradientFromDeltaR
  forwardDerivative = derivativeFromDeltaR
  unlet = runlet

gradientFromDeltaR
  :: (KnownNat y, GoodScalar r, ADReady ranked)
  => VoidHVector
  -> ranked r y -> Maybe (ranked r y) -> DeltaR ranked r y
  -> (AstBindingsD ranked, HVector ranked)
gradientFromDeltaR !parameters0 value !mdt !deltaTopLevel =
  let dt = fromMaybe (rreplicate0N (rshape value) 1) mdt
      s0 = initEvalState parameters0
      s1 = evalR s0 dt deltaTopLevel
      EvalState{..} = evalFromnMap s1
      !gradient = V.fromList $ EM.elems iMap
  in (astBindings, gradient)

derivativeFromDeltaR
  :: forall ranked r n.
     (KnownNat n, GoodScalar r, ADReady ranked)
  => Int -> DeltaR ranked r n -> HVector ranked
  -> (AstBindingsD ranked, ranked r n)
derivativeFromDeltaR dim deltaTopLevel ds =
  let s0 = EvalState EM.empty EM.empty EM.empty EM.empty EM.empty []
      !(!s2, !c) = fwdR dim ds s0 deltaTopLevel
  in (astBindings s2, c)

instance ADReadyS shaped => DualPart @[Nat] shaped where
  type Dual shaped = DeltaS shaped
  reverseDervative parameters0 _ = gradientFromDeltaS parameters0
  forwardDerivative = derivativeFromDeltaS
  unlet = sunlet

gradientFromDeltaS
  :: forall shaped r y.
     (Sh.Shape y, GoodScalar r, ADReadyS shaped)
  => VoidHVector
  -> Maybe (shaped r y) -> DeltaS shaped r y
  -> (AstBindingsD (RankedOf shaped), HVector (RankedOf shaped))
gradientFromDeltaS !parameters0 !mdt !deltaTopLevel =
  let dt = fromMaybe 1 mdt
      s0 = initEvalState parameters0
      s1 = evalS s0 dt deltaTopLevel
      EvalState{..} = evalFromnMap s1
      !gradient = V.fromList $ EM.elems iMap
  in (astBindings, gradient)

derivativeFromDeltaS
  :: forall shaped r sh.
     (Sh.Shape sh, GoodScalar r, ADReadyS shaped)
  => Int -> DeltaS shaped r sh -> HVector (RankedOf shaped)
  -> (AstBindingsD (RankedOf shaped), shaped r sh)
derivativeFromDeltaS !dim !deltaTopLevel !ds =
  let s0 = EvalState EM.empty EM.empty EM.empty EM.empty EM.empty []
      !(!s2, !c) = fwdS dim ds s0 deltaTopLevel
  in (astBindings s2, c)

instance ADReady ranked => DualPart @() (HVectorPseudoTensor ranked) where
  type Dual (HVectorPseudoTensor ranked) = HVectorPseudoTensor (DeltaR ranked)
  reverseDervative = gradientFromDeltaH
  forwardDerivative = derivativeFromDeltaH
  unlet l astBindings =
    HVectorPseudoTensor . dunlet l astBindings . unHVectorPseudoTensor

-- @r@ is a placeholder here, it's reduced away. @y@ is '(), but GHC doesn't
-- know it has to be that. We could instead provide a type-level list of nats
-- and lists of nats or at least the length of the list, and a list
-- of the scalar types, but the shaped typing is too complex already.
gradientFromDeltaH
  :: forall ranked r (y :: ()). ADReady ranked
  => VoidHVector
  -> HVectorPseudoTensor ranked r y
  -> Maybe (HVectorPseudoTensor ranked r y)
  -> HVectorPseudoTensor (DeltaR ranked) r y
  -> (AstBindingsD ranked, HVector ranked)
gradientFromDeltaH !parameters0 (HVectorPseudoTensor value)
                   !mdt !(HVectorPseudoTensor deltaTopLevel) =
  let shDt = dshape @ranked value
      dt :: HVectorOf ranked
      dt = maybe (dmkHVector $ mapHVectorShaped @(ShapedOf ranked) (const 1)
                  $ V.map dynamicFromVoid shDt)
                 unHVectorPseudoTensor
                 mdt
      s0 = initEvalState parameters0
      (abShared, dtShared) =  -- really not to share, but to convert to HVector
        dregister shDt dt (astBindings s0)
      sShared = s0 {astBindings = abShared}
      s1 = evalH sShared dtShared deltaTopLevel
      EvalState{astBindings=astB, ..} = evalFromnMap s1
      !gradient = V.fromList $ EM.elems iMap
  in (astB, gradient)

-- @r@ is a placeholder here, it's reduced away. @y@ is '(), but GHC doesn't
-- know it has to be that.
derivativeFromDeltaH
  :: forall ranked r (y :: ()). ADReady ranked
  => Int
  -> HVectorPseudoTensor (DeltaR ranked) r y
  -> HVector ranked
  -> (AstBindingsD ranked, HVectorPseudoTensor ranked r y)
derivativeFromDeltaH dim (HVectorPseudoTensor deltaTopLevel) ds =
  let s0 = EvalState EM.empty EM.empty EM.empty EM.empty EM.empty []
      !(!s2, !c) = fwdH dim ds s0 deltaTopLevel
  in (astBindings s2, HVectorPseudoTensor c)


-- * Reverse pass, transpose/evaluation of the delta expressions

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
  { iMap        :: EM.EnumMap (InputId ranked) (DynamicTensor ranked)
      -- ^ eventually, cotangents of objective function inputs
      -- (eventually copied to the vector representing the gradient
      -- of the objective function);
      -- the identifiers need to be contiguous and start at 0
  , dMap        :: EM.EnumMap (NodeId ranked) (DynamicTensor ranked)
      -- ^ eventually, cotangents of non-input subterms indexed
      -- by their node identifiers
  , nMap        :: EM.EnumMap (NodeId ranked) (DynamicTensor (DeltaR ranked))
      -- ^ nodes left to be evaluated;
      -- we can't evaluate them at once, because their other shared copies
      -- may still not be processed, so we'd not take advantage of the sharing
      -- and not take into account the whole summed context when finally
      -- evaluating
  , hdMap       :: EM.EnumMap (NodeId ranked) (HVector ranked)
  , hnMap       :: EM.EnumMap (NodeId ranked) (DeltaH ranked)
  , astBindings :: AstBindingsD ranked
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
  let iMap = EM.fromDistinctAscList $ zip [toInputId 0 ..]
             $ map dynamicFromVoid $ V.toList parameters0
      dMap = EM.empty
      nMap = EM.empty
      hdMap = EM.empty
      hnMap = EM.empty
      astBindings = []
  in EvalState {..}

-- The first argument is the evaluation state being modified,
-- the second is the cotangent accumulator that will become an actual
-- cotangent contribution when complete (see below for an explanation)
-- and the third argument is the node to evaluate.
evalRRuntimeSpecialized
  :: forall n r ranked shaped.
     (KnownNat n, GoodScalar r, ADReady ranked, shaped ~ ShapedOf ranked)
  => EvalState ranked
  -> ranked r n -> DeltaR ranked r n
  -> EvalState ranked
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
          _ -> error "evalRRuntimeSpecialized: unexpected scalar"

evalDynamic
  :: (ADReady ranked, shaped ~ ShapedOf ranked)
  => EvalState ranked
  -> (DynamicTensor ranked, DynamicTensor (DeltaR ranked))
  -> EvalState ranked
evalDynamic s3 (t, DynamicRanked d2) = evalR s3 (rfromD t) d2
evalDynamic s3 (t, DynamicShaped d2) = evalS s3 (sfromD t) d2
evalDynamic s3 (t, DynamicRankedDummy @r @sh _ _) =
  withListShape (Sh.shapeT @sh) $ \(sh2 :: ShapeInt n) ->
    gcastWith (unsafeCoerce Refl :: Sh.Rank sh :~: n) $
    evalR @_ @r s3 (rfromD t) (ZeroR sh2)
evalDynamic s3 (t, DynamicShapedDummy @r @sh _ _) =
  evalS @sh @r s3 (sfromD t) ZeroS

evalHVector
  :: (ADReady ranked, shaped ~ ShapedOf ranked)
  => EvalState ranked -> HVector ranked -> HVector (DeltaR ranked)
  -> EvalState ranked
evalHVector s as as' = V.foldl' evalDynamic s $ V.zip as as'

evalR
  :: forall n r ranked shaped.
     (KnownNat n, GoodScalar r, ADReady ranked, shaped ~ ShapedOf ranked)
  => EvalState ranked -> ranked r n -> DeltaR ranked r n
  -> EvalState ranked
evalR !s !c = let (abShared, cShared) = rregister c (astBindings s)
                  sShared = s {astBindings = abShared}
              in \case
  ZeroR{} -> s
  InputR _ i -> s {iMap = EM.adjust (DynamicRanked . raddDynamic c) i
                          $ iMap s}
    -- This and similar don't need to be runtime-specialized,
    -- because the type of c determines the Num instance for (+).
    -- Note that we can't express sharing by inserting Let constructors
    -- into iMap, because often sharing needs to work across many
    -- iMap keys. That's why global sharing is used, via rregister.
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
        Just (DynamicRanked _) ->
          s {dMap = EM.adjust (DynamicRanked
                               . raddDynamic c) n $ dMap s}
        Nothing ->
          let cs = DynamicRanked c
          in s { nMap = EM.insert n (DynamicRanked d) $ nMap s
               , dMap = EM.insert n cs $ dMap s }
        _ -> error "evalR: corrupted nMap"

  IndexR d ix -> evalR s (rscatter @ranked @r @0
                                       (shapeDeltaR d) c (const ix)) d
    -- equivalent: evalR s (updateNR (treplicate0NR sh 0) [(ix, c)]) d
  SumR d -> evalR s (rreplicate (lengthDeltaR d) c) d
  Sum0R d -> evalR s (rreplicate0N (shapeDeltaR d) c) d
  Dot0R v vd -> evalR s (v * rreplicate0N (rshape v) c) vd
               -- too slow: evalR s (rmap0N (* (tscalar c)) v) vd
  ScatterR _sh d f -> evalR s (rgather (shapeDeltaR d) c f) d

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
    n :$ _ -> let k = lengthDeltaR d
                  s2 = evalR sShared (rslice 0 k cShared) d
              in evalR s2 (rslice k (n - k) cShared) e
    ZS -> error "evalR: impossible pattern needlessly required"
  SliceR i n d -> case rshape c of
    n' :$ rest ->
      assert (n' == n `blame` (n', n)) $
      evalR s (rconcat [ rzero (i :$ rest)
                       , c
                       , rzero (lengthDeltaR d - i - n :$ rest) ])
              d
    ZS -> error "evalR: impossible pattern needlessly required"
  ReverseR d -> evalR s (rreverse c) d
  TransposeR perm d ->
    let perm_reversed = map snd $ sort $ zip perm [0 .. length perm - 1]
    in evalR s (rtranspose perm_reversed c) d
  ReshapeR _sh d -> evalR s (rreshape (shapeDeltaR d) c) d
  GatherR _sh d f -> evalR s (rscatter (shapeDeltaR d) c f) d

  CastR d -> evalRRuntimeSpecialized s (rcast c) d

  RFromS (SFromR d) -> evalR s c d  -- no information lost, so no checks
  RFromS d -> evalS s (sfromR c) d
  RFromH d i ->
    let cs = V.map dynamicFromVoid $ shapeDeltaH d
        ci = DynamicRanked c
    in assert (dynamicsMatch (cs V.! i) ci) $
       evalH s (cs V.// [(i, ci)]) d
      -- should be used only with small vectors or we end up with the same
      -- problem of summing a lot of one-hots as in indexing

evalSRuntimeSpecialized
  :: forall sh r ranked shaped.
     (Sh.Shape sh, GoodScalar r, ADReady ranked, shaped ~ ShapedOf ranked)
  => EvalState ranked -> shaped r sh -> DeltaS shaped r sh
  -> EvalState ranked
evalSRuntimeSpecialized !s !c =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalS @sh @Double s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalS @sh @Float s c
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> evalS @sh @Int64 s c
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> evalS @sh @CInt s c
          _ -> error "evalSRuntimeSpecialized: unexpected scalar"

evalS
  :: forall sh r ranked shaped.
     (Sh.Shape sh, GoodScalar r, ADReady ranked, shaped ~ ShapedOf ranked)
  => EvalState ranked -> shaped r sh -> DeltaS shaped r sh
  -> EvalState ranked
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
        Just (DynamicShaped _) ->
          s {dMap = EM.adjust (DynamicShaped . saddDynamic c) n $ dMap s}
        Nothing ->
          let cs = DynamicShaped c
          in s { nMap = EM.insert n (DynamicShaped d) $ nMap s
               , dMap = EM.insert n cs $ dMap s }
        _ -> error "evalS: corrupted nMap"

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
  CastS d -> evalSRuntimeSpecialized s (scast c) d
  SFromR (RFromS @sh2 d) ->
    case sameShape @sh @sh2 of
      Just Refl -> evalS s c d
      _ -> error "evalS: different shapes in SFromR(RFromS)"
  SFromR d -> evalR s (rfromS c) d
  SFromH d i ->
    let cs = V.map dynamicFromVoid $ shapeDeltaH d
        ci = DynamicShaped c
    in assert (dynamicsMatch (cs V.! i) ci) $
       evalH s (cs V.// [(i, ci)]) d

evalH
  :: forall ranked shaped. (ADReady ranked, shaped ~ ShapedOf ranked)
  => EvalState ranked -> HVector ranked -> DeltaH ranked
  -> EvalState ranked
evalH !s !c = let (abShared, cShared) =
                    dregister (voidFromHVector c) (dmkHVector c) (astBindings s)
                  sShared = s {astBindings = abShared}
              in \case
  LetH n d ->
    assert (case d of
              LetH{} -> False  -- wasteful and nonsensical
              _ -> True)
    $ case EM.lookup n $ hnMap s of
        Just{} ->
          s {hdMap = EM.adjust (V.zipWith addDynamic c) n $ hdMap s}
        Nothing ->
          s { hnMap = EM.insert n d $ hnMap s
            , hdMap = EM.insert n c $ hdMap s }
  HToH v -> evalHVector s c v
  MapAccumR k accShs bShs eShs q es _df rf acc0' es' ->
    let accLen = V.length accShs
        bLen = V.length bShs
        (c0, crest) = V.splitAt accLen cShared
        dacc_desUnshared =
          dmapAccumL k accShs eShs (bShs V.++ accShs V.++ eShs)
                     (\dx db_acc_e ->
                        let (db, acc_e) = V.splitAt bLen db_acc_e
                        in unHFun rf [dx V.++ db, acc_e])
                     c0
                     (V.concat [crest, q, es])
        (abShared2, dacc_des) =
          dregister (accShs V.++ voidFromHVector es)
                    dacc_desUnshared (astBindings sShared)
        s2 = sShared {astBindings = abShared2}
        (dacc, des) = V.splitAt accLen dacc_des
        s3 = evalHVector s2 dacc acc0'
    in evalHVector s3 des es'
  MapAccumL k accShs bShs eShs q es _df rf acc0' es' ->
    let accLen = V.length accShs
        bLen = V.length bShs
        (c0, crest) = V.splitAt accLen cShared
        dacc_desUnshared =
          dmapAccumR k accShs eShs (bShs V.++ accShs V.++ eShs)
                     (\dx db_acc_e ->
                        let (db, acc_e) = V.splitAt bLen db_acc_e
                        in unHFun rf [dx V.++ db, acc_e])
                     c0
                     (V.concat [crest, q, es])
        (abShared2, dacc_des) =
          dregister (accShs V.++ voidFromHVector es)
                    dacc_desUnshared (astBindings sShared)
        s2 = sShared {astBindings = abShared2}
        (dacc, des) = V.splitAt accLen dacc_des
        s3 = evalHVector s2 dacc acc0'
    in evalHVector s3 des es'

evalFromnMap :: (ADReady ranked, shaped ~ ShapedOf ranked)
             => EvalState ranked -> EvalState ranked
evalFromnMap s@EvalState{nMap, dMap, hnMap, hdMap} =
  -- We discharge the non-vector cases before the vector ones, because
  -- the latter tend to create and store more cases and so enlarge
  -- the working set of cases.
  case EM.maxViewWithKey nMap of
    Just ((n, b), nMap2) ->
      let s2 = s {nMap = nMap2}
          s3 = case b of
            DynamicRanked @r1 @n1 d -> case dMap EM.! n of
              DynamicRanked @r2 @n2 c -> case sameNat (Proxy @n2)
                                                      (Proxy @n1) of
                Just Refl -> case testEquality (typeRep @r1)
                                               (typeRep @r2) of
                  Just Refl -> evalRRuntimeSpecialized s2 c d
                  _ -> error "evalFromnMap: scalar mismatch"
                _ -> error "evalFromnMap: rank mismatch"
              DynamicShaped{} ->
                error "evalFromnMap: DynamicShaped"
              DynamicRankedDummy{} ->
                error "evalFromnMap: DynamicRankedDummy"
              DynamicShapedDummy{} ->
                error "evalFromnMap: DynamicShapedDummy"
            DynamicShaped @r1 @sh1 d -> case dMap EM.! n of
              DynamicRanked{} ->
                error "evalFromnMap: DynamicRanked"
              DynamicShaped @r2 @sh2 c -> case sameShape @sh2 @sh1 of
                Just Refl -> case testEquality (typeRep @r1)
                                               (typeRep @r2) of
                  Just Refl -> evalSRuntimeSpecialized s2 c d
                  _ -> error "evalFromnMap: scalar mismatch"
                _ -> error "evalFromnMap: shape mismatch"
              DynamicRankedDummy{} ->
                error "evalFromnMap: DynamicRankedDummy"
              DynamicShapedDummy{} ->
                error "evalFromnMap: DynamicShapedDummy"
            _ -> error "evalFromnMap: corrupted nMap"
      in evalFromnMap s3
    Nothing -> case EM.maxViewWithKey hnMap of
      Just ((n, d), hnMap2) ->
        let s2 = s {hnMap = hnMap2}
            s3 = evalH s2 (hdMap EM.! n) d
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
          in s {iMap = EM.adjust f i $ iMap s}
        Index0 (LetR n d) ixs' sh ->
          let ixs = indexToList ixs'
          in case EM.lookup n $ nMap s of
            Just (DynamicRanked _) ->
              let f v = v `OD.update` [(ixs, v `rindex0D` ixs + c)]
              in s {dMap = EM.adjust f n $ dMap s}
                -- This would be an asymptotic optimization compared to
                -- the general case below, if not for the non-mutable update,
                -- which implies copying the whole @v@ vector,
                -- so it's only several times faster (same allocation,
                -- but not adding to each cell of @v@).
            Nothing ->
              let v = treplicate0ND sh 0 `OD.update` [(ixs, c)]
              in s { nMap = EM.insert n (DynamicRanked d) $ nMap s
                   , dMap = EM.insert n v $ dMap s }
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
  :: forall ranked shaped. (ADReady ranked, shaped ~ ShapedOf ranked)
  => Int -> HVector ranked
  -> EvalState ranked
  -> DynamicTensor (DeltaR ranked)
  -> (EvalState ranked, DynamicTensor ranked)
fwdDynamic dimR params s (DynamicRanked d) =
  second DynamicRanked $ fwdR dimR params s d
fwdDynamic dimR params s (DynamicShaped d) =
  second DynamicShaped $ fwdS dimR params s d
fwdDynamic dimR params s (DynamicRankedDummy @r @sh _ _) =
  withListShape (Sh.shapeT @sh) $ \(sh2 :: ShapeInt n) ->
    gcastWith (unsafeCoerce Refl :: Sh.Rank sh :~: n) $
    second (DynamicRanked @r @n) $ fwdR dimR params s (ZeroR sh2)
fwdDynamic dimR params s (DynamicShapedDummy @r @sh _ _) =
  second (DynamicShaped @r @sh) $ fwdS dimR params s ZeroS

fwdHVector
  :: forall ranked shaped. (ADReady ranked, shaped ~ ShapedOf ranked)
  => Int -> HVector ranked
  -> EvalState ranked
  -> HVector (DeltaR ranked)
  -> (EvalState ranked, HVector ranked)
fwdHVector dimR params = mapAccumL (fwdDynamic dimR params)

fwdR
  :: forall n r ranked shaped.
     (KnownNat n, GoodScalar r, ADReady ranked, shaped ~ ShapedOf ranked)
  => Int -> HVector ranked -> EvalState ranked -> DeltaR ranked r n
  -> (EvalState ranked, ranked r n)
fwdR dimR params s = \case
  ZeroR sh -> (s, rzero sh)
  InputR _ (InputId i) ->
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
  LetR n d ->
    case EM.lookup n $ nMap s of
      Just (DynamicRanked _) ->
        case dMap s EM.! n of
          DynamicRanked @r2 @n2 e -> case sameNat (Proxy @n2)
                                                  (Proxy @n) of
            Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
              Just Refl -> (s, e)
              _ -> error "fwdR: scalar mismatch"
            _ -> error "fwdR: rank mismatch"
          DynamicShaped{} -> error "fwdR: DynamicShaped"
          DynamicRankedDummy{} ->
            error "fwdR: DynamicRankedDummy"
          DynamicShapedDummy{} ->
            error "fwdR: DynamicShapedDummy"
      Nothing ->
        let (s2, cRaw) = fwdR dimR params s d
            (abShared, cShared) = rregister cRaw (astBindings s2)
            s3 = s2 {astBindings = abShared}
            s4 = s3 { nMap = EM.insert n (DynamicRanked d) (nMap s3)
                    , dMap = EM.insert n (DynamicRanked cShared)
                                         (dMap s3) }
        in (s4, cShared)
      _ -> error "fwdR: corrupted nMap"

  IndexR d ix -> second (`rindex` ix) $ fwdR dimR params s d
  SumR d -> second rsum $ fwdR dimR params s d
  Sum0R ZeroR{} -> (s, 0)
  Sum0R d -> second rsum0 $ fwdR dimR params s d
  Dot0R _ ZeroR{} -> (s, 0)
  Dot0R v d -> second (rdot0 v) $ fwdR dimR params s d
  ScatterR sh d f ->
    let (s2, t) = fwdR dimR params s d
    in (s2, rscatter sh t f)

  FromListR lsd ->
    let (s2, l) = mapAccumL (fwdR dimR params) s lsd
    in (s2, rfromList l)
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
  RFromS d -> second rfromS $ fwdS dimR params s d
  RFromH d i -> let (s2, v) = fwdH dimR params s d
                    doms = shapeDeltaH d
                in (s2, rletHVectorIn doms v $ \res ->
                          rfromD $ res V.! i)

fwdS
  :: forall sh r ranked shaped.
     (Sh.Shape sh, GoodScalar r, ADReady ranked, shaped ~ ShapedOf ranked)
  => Int -> HVector ranked -> EvalState ranked -> DeltaS shaped r sh
  -> (EvalState ranked, shaped r sh)
fwdS dimR params s = \case
  ZeroS -> (s, 0)
  InputS (InputId i) ->
    if i < dimR
    then case params V.! i of
      DynamicRanked{} -> error "fwdS: DynamicRanked"
      DynamicShaped @r2 @sh2 e -> case sameShape @sh2 @sh of
        Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> (s, e)
          _ -> error "fwdS: scalar mismatch"
        _ -> error "fwdS: shape mismatch"
      DynamicRankedDummy{} -> error "fwdS: DynamicRankedDummy"
      DynamicShapedDummy{} -> error "fwdS: DynamicShapedDummy"
    else error "fwdS: wrong index for an input"
  ScaleS k d -> second (* k) $ fwdS dimR params s d
  AddS d e -> let (s2, t) = fwdS dimR params s d
                  (s3, u) = fwdS dimR params s2 e
              in (s3, t + u)
  LetS n d ->
    case EM.lookup n $ nMap s of
      Just (DynamicShaped _) ->
        case dMap s EM.! n of
          DynamicRanked{} -> error "fwdS: DynamicRanked"
          DynamicShaped @r2 @sh2 e -> case sameShape @sh2 @sh of
            Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
              Just Refl -> (s, e)
              _ -> error "fwdS: scalar mismatch"
            _ -> error "fwdS: shape mismatch"
          DynamicRankedDummy{} ->
            error "fwdS: DynamicRankedDummy"
          DynamicShapedDummy{} ->
            error "fwdS: DynamicShapedDummy"
      Nothing ->
        let (s2, cRaw) = fwdS dimR params s d
            (abShared, cShared) = sregister cRaw (astBindings s2)
            s3 = s2 {astBindings = abShared}
            s4 = s3 { nMap = EM.insert n (DynamicShaped d) (nMap s3)
                    , dMap = EM.insert n (DynamicShaped cShared)
                                         (dMap s3) }
        in (s4, cShared)
      _ -> error "fwdS: corrupted nMap"

  IndexS d ix -> second (`sindex` ix) $ fwdS dimR params s d
  SumS d -> second ssum $ fwdS dimR params s d
  Sum0S ZeroS -> (s, 0)
  Sum0S d -> second ssum0 $ fwdS dimR params s d
  Dot0S _ ZeroS -> (s, 0)
  Dot0S v d -> second (sdot0 v) $ fwdS dimR params s d
  ScatterS d f ->
    let (s2, t) = fwdS dimR params s d
    in (s2, sscatter t f)

  FromListS lsd ->
    let (s2, l) = mapAccumL (fwdS dimR params) s lsd
    in (s2, sfromList l)
  FromVectorS lsd ->
    let (s2, l) = mapAccumL (fwdS dimR params) s lsd
    in (s2, sfromVector l)
  ReplicateS d ->
    let (s2, t) = fwdS dimR params s d
    in (s2, sreplicate t)
  AppendS d e ->
    let (s2, t) = fwdS dimR params s d
        (s3, u) = fwdS dimR params s2 e
    in (s3, sappend t u)
  SliceS @_ @i d -> second (sslice (Proxy @i) Proxy) $ fwdS dimR params s d
  ReverseS d -> second sreverse $ fwdS dimR params s d
  TransposeS @_ @perm d -> second (stranspose (Proxy @perm))
                           $ fwdS dimR params s d
  ReshapeS d -> second sreshape $ fwdS dimR params s d
  GatherS d f ->
    let (s2, t) = fwdS dimR params s d
    in (s2, sgather t f)
  CastS d ->
    second scast $ fwdS dimR params s d

  SFromR (RFromS @sh2 d) ->
    case sameShape @sh @sh2 of
      Just Refl -> fwdS dimR params s d
      _ -> error "fwdS: different shapes in SFromR(RFromS)"
  SFromR d -> second sfromR $ fwdR dimR params s d
  SFromH d i -> let (s2, v) = fwdH dimR params s d
                    doms = shapeDeltaH d
                in (s2, sletHVectorIn doms v $ \res ->
                          sfromD $ res V.! i)

fwdH
  :: forall ranked shaped. (ADReady ranked, shaped ~ ShapedOf ranked)
  => Int -> HVector ranked -> EvalState ranked -> DeltaH ranked
  -> (EvalState ranked, HVectorOf ranked)
fwdH dimR params s = \case
  LetH n d ->
    case EM.lookup n $ hnMap s of
      Just{} -> (s, dmkHVector $ hdMap s EM.! n)
      Nothing ->
        let (s2, cRaw) = fwdH dimR params s d
            (abShared, cShared) =
              dregister (shapeDeltaH d) cRaw (astBindings s2)
            s3 = s2 {astBindings = abShared}
            s4 = s3 { hnMap = EM.insert n d (hnMap s3)
                    , hdMap = EM.insert n cShared (hdMap s3) }
        in (s4, dmkHVector cShared)
  HToH v -> second dmkHVector $ fwdHVector dimR params s v
  MapAccumR k accShs bShs eShs q es df _rf acc0' es' ->
    let (s2, cacc0) = fwdHVector dimR params s acc0'
        (s3, ces) = fwdHVector dimR params s2 es'
        eLen = V.length eShs
    in (s3, dmapAccumR k accShs bShs (eShs V.++ accShs V.++ eShs)
                       (\dacc de_acc_e ->
                          let (de, acc_e) = V.splitAt eLen de_acc_e
                          in unHFun df [dacc V.++ de, acc_e])
                       cacc0
                       (V.concat [ces, q, es]))
  MapAccumL k accShs bShs eShs q es df _rf acc0' es' ->
    let (s2, cacc0) = fwdHVector dimR params s acc0'
        (s3, ces) = fwdHVector dimR params s2 es'
        eLen = V.length eShs
    in (s3, dmapAccumL k accShs bShs (eShs V.++ accShs V.++ eShs)
                       (\dacc de_acc_e ->
                          let (de, acc_e) = V.splitAt eLen de_acc_e
                          in unHFun df [dacc V.++ de, acc_e])
                       cacc0
                       (V.concat [ces, q, es]))


-- * Manually fixed Show instances

instance (KnownNat n0,
          GoodScalar r0,
          Show (IntOf ranked),
          Show
            (IntOf
               (ShapedOf ranked)),
          CRanked ranked Show,
          CShaped
            (ShapedOf ranked)
            Show,
          CShaped
            (DeltaS
               (ShapedOf ranked))
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
  showsPrec a_adki (CastR b1_adkj)
    = showParen
        (a_adki >= 11)
        ((.)
           (showString "CastR ") (showsPrec 11 b1_adkj))
  showsPrec a_adkk (RFromS b1_adkl)
    = showParen
        (a_adkk >= 11)
        ((.)
           (showString "RFromS ") (showsPrec 11 b1_adkl))
  showsPrec
    a_a2Gg0
    (HordeAd.Core.Delta.RFromH b1_a2Gg1 b2_a2Gg2)
    = showParen
        (a_a2Gg0 >= 11)
        ((.)
           (showString "RFromH ")
           ((.)
              (showsPrec 11 b1_a2Gg1)
              ((.)
                 showSpace (showsPrec 11 b2_a2Gg2))))

instance (ShapedOf (RankedOf shaped) ~ shaped,
          Sh.Shape sh0,
          GoodScalar r0,
          Show
            (IntOf
               (RankedOf shaped)),
          Show
            (IntOf shaped),
          CRanked
            (RankedOf shaped)
            Show,
          CShaped shaped Show,
          CRanked
            (DeltaR
               (RankedOf shaped))
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
  showsPrec a_adv6 (CastS b1_adv7)
    = showParen
        (a_adv6 >= 11)
        ((.)
           (showString "CastS ") (showsPrec 11 b1_adv7))
  showsPrec a_adv8 (SFromR b1_adv9)
    = showParen
        (a_adv8 >= 11)
        ((.)
           (showString "SFromR ") (showsPrec 11 b1_adv9))
  showsPrec
    a_a2Gei
    (HordeAd.Core.Delta.SFromH b1_a2Gej b2_a2Gek)
    = showParen
        (a_a2Gei >= 11)
        ((.)
           (showString "SFromH ")
           ((.)
              (showsPrec 11 b1_a2Gej)
              ((.)
                 showSpace (showsPrec 11 b2_a2Gek))))

instance (Show
            (HordeAd.Core.Types.IntOf ranked),
          Show
            (HordeAd.Core.Types.IntOf
               (HordeAd.Core.Types.ShapedOf ranked)),
          HordeAd.Core.HVector.CRanked ranked Show,
          HordeAd.Core.HVector.CShaped
            (HordeAd.Core.Types.ShapedOf ranked)
            Show,
          HordeAd.Core.HVector.CRanked
            (HordeAd.Core.Delta.DeltaR ranked) Show,
          HordeAd.Core.HVector.CShaped
            (HordeAd.Core.Delta.DeltaS
               (HordeAd.Core.Types.ShapedOf ranked))
            Show) =>
         Show (HordeAd.Core.Delta.DeltaH ranked) where
  showsPrec
    a_a2Gc8
    (HordeAd.Core.Delta.LetH b1_a2Gc9 b2_a2Gca)
    = showParen
        (a_a2Gc8 >= 11)
        ((.)
           (showString "LetH ")
           ((.)
              (showsPrec 11 b1_a2Gc9)
              ((.)
                 showSpace (showsPrec 11 b2_a2Gca))))
  showsPrec a_a2Gcb (HordeAd.Core.Delta.HToH b1_a2Gcc)
    = showParen
        (a_a2Gcb >= 11)
        ((.)
           (showString "HToH ") (showsPrec 11 b1_a2Gcc))
