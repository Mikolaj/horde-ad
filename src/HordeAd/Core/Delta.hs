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
  ( -- * Delta identifiers
    NodeId, mkNodeId, nodeIdToSTK
  , InputId, mkInputId, inputIdToSTK
    -- * AST of delta expressions
  , Delta(..)
    -- * Full tensor kind derivation for delta expressions
  , ftkDelta
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import Data.Some
import Data.Type.Equality
  (TestEquality (..), gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Data.Vector.Strict qualified as Data.Vector
import GHC.TypeLits (type (+), type (<=))
import Text.Show.Functions ()
import Type.Reflection (typeRep)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
  (shxAppend, shxDropSSX, shxTakeSSX, ssxFromShape, withKnownShX)
import Data.Array.Mixed.Types (snatPlus, unsafeCoerceRefl)
import Data.Array.Nested
  ( IShR
  , IShX
  , MapJust
  , Rank
  , Replicate
  , ShR (..)
  , ShS (..)
  , ShX (..)
  , StaticShX (..)
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape
  ( ixrRank
  , shCvtRX
  , shCvtSX
  , shCvtXR'
  , shrTail
  , shsAppend
  , shsPermutePrefix
  , shsRank
  )
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Delta identifiers

type role NodeId nominal nominal
data NodeId :: Target -> TensorKindType -> Type where
  NodeId :: forall target y. KnownSTK y => Int -> NodeId target y

-- No Eq instance to limit hacks outside this module.

instance Show (NodeId target y) where
  showsPrec d (NodeId n) =
    showsPrec d n  -- less verbose, more readable

instance DMap.Enum1 (NodeId target) where
  type Enum1Info (NodeId target) = Some (Dict KnownSTK)
  fromEnum1 (NodeId @_ @a n) = (n, Some @_ @a Dict)
  toEnum1 n (Some @_ @a Dict) = Some $ NodeId @target @a n

instance TestEquality (NodeId target) where
  testEquality (NodeId @_ @y1 _) (NodeId @_ @y2 _) = sameKnownSTK @y1 @y2

-- | Wrap non-negative (only!) integers in the `NodeId` newtype.
mkNodeId :: STensorKind y -> Int -> NodeId f y
mkNodeId stk i | Dict <- lemKnownSTK stk =
  assert (i >= 0) $ NodeId i

nodeIdToSTK :: NodeId f y -> STensorKind y
nodeIdToSTK (NodeId _) = knownSTK

type role InputId nominal nominal
data InputId :: Target -> TensorKindType -> Type where
  InputId :: forall target y. KnownSTK y => Int -> InputId target y

-- No Eq instance to limit hacks outside this module.

deriving instance Show (InputId target y)

instance DMap.Enum1 (InputId target) where
  type Enum1Info (InputId target) = Some (Dict KnownSTK)
  fromEnum1 (InputId @_ @a n) = (n, Some @_ @a Dict)
  toEnum1 n (Some @_ @a Dict) = Some $ InputId @target @a n

instance TestEquality (InputId target) where
  testEquality (InputId @_ @y1 _) (InputId @_ @y2 _) = sameKnownSTK @y1 @y2

-- | Wrap non-negative (only!) integers in the `InputId` newtype.
mkInputId :: STensorKind y -> Int -> InputId f y
mkInputId stk i | Dict <- lemKnownSTK stk =
  assert (i >= 0) $ InputId i

inputIdToSTK :: InputId f y -> STensorKind y
inputIdToSTK (InputId _) = knownSTK


-- * AST of delta expressions

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
-- The `NodeId` identifier that appears in a @DeltaShare n d@ expression
-- is the unique identity stamp of subterm @d@, that is, there is
-- no different term @e@ such that @DeltaShare n e@ appears in any delta
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
-- any term containing a function (e.g., a @DeltaGather@ node)
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

type role Delta nominal nominal
data Delta :: Target -> TensorKindType -> Type where
  -- General operations, for scalar, ranked, shared and other tensors at once
  DeltaPair :: forall y z target.
               Delta target y -> Delta target z
            -> Delta target (TKProduct y z)
  DeltaProject1 :: forall y z target.
                   Delta target (TKProduct y z) -> Delta target y
  DeltaProject2 :: forall y z target.
                   Delta target (TKProduct y z) -> Delta target z
  DeltaFromVector :: forall y k target.
                     SNat k -> STensorKind y
                  -> Data.Vector.Vector (Delta target y)
                  -> Delta target (BuildTensorKind k y)
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  DeltaSum :: forall y k target.
              SNat k -> STensorKind y
           -> Delta target (BuildTensorKind k y)
           -> Delta target y
  DeltaReplicate :: forall y k target.
                    SNat k -> STensorKind y
                 -> Delta target y
                 -> Delta target (BuildTensorKind k y)
    -- ^ Copy the given tensor along the new, outermost dimension.
  DeltaMapAccumR
    :: forall target k accShs bShs eShs.
       ( Show (target (BuildTensorKind k accShs))
       , Show (target (BuildTensorKind k eShs)) )
    => SNat k
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> target (BuildTensorKind k accShs)
    -> target (BuildTensorKind k eShs)
    -> HFun (TKProduct (ADTensorKind (TKProduct accShs eShs))
                       (TKProduct accShs eShs))
            (ADTensorKind (TKProduct accShs bShs))
    -> HFun (TKProduct (ADTensorKind (TKProduct accShs bShs))
                       (TKProduct accShs eShs))
            (ADTensorKind (TKProduct accShs eShs))
    -> Delta target accShs
    -> Delta target (BuildTensorKind k eShs)
    -> Delta target (TKProduct accShs (BuildTensorKind k bShs))
  DeltaMapAccumL
    :: forall target k accShs bShs eShs.
       ( Show (target (BuildTensorKind k accShs))
       , Show (target (BuildTensorKind k eShs)) )
    => SNat k
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> target (BuildTensorKind k accShs)
    -> target (BuildTensorKind k eShs)
    -> HFun (TKProduct (ADTensorKind (TKProduct accShs eShs))
                       (TKProduct accShs eShs))
            (ADTensorKind (TKProduct accShs bShs))
    -> HFun (TKProduct (ADTensorKind (TKProduct accShs bShs))
                       (TKProduct accShs eShs))
            (ADTensorKind (TKProduct accShs eShs))
    -> Delta target accShs
    -> Delta target (BuildTensorKind k eShs)
    -> Delta target (TKProduct accShs (BuildTensorKind k bShs))

  -- Sharing-related operations
  DeltaShare :: NodeId target y -> Delta target y -> Delta target y
  DeltaInput :: forall target y.
                FullTensorKind y -> InputId target y -> Delta target y

  -- Vector space operations
  DeltaZero :: FullTensorKind y -> Delta target y
  DeltaScale :: (Num (target y), Show (target y))
             => target y -> Delta target y -> Delta target y
  DeltaAdd :: Num (target y)
           => Delta target y -> Delta target y -> Delta target y

  -- Scalar arithmetic
  DeltaCastK :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2)
             => Delta target (TKScalar r1) -> Delta target (TKScalar r2)

  -- Ranked tensor operations
  DeltaCastR :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2)
             => Delta target (TKR n r1) -> Delta target (TKR n r2)
  DeltaSum0R :: Delta target (TKR2 n r) -> Delta target (TKR2 0 r)
  DeltaDot0R :: (GoodScalar r, Show (target (TKR n r)))
             => target (TKR n r) -> Delta target (TKR n r)
             -> Delta target (TKR 0 r)
  DeltaIndexR :: forall m n r target.
                 SNat n
              -> Delta target (TKR2 (m + n) r) -> IxROf target m
              -> Delta target (TKR2 n r)
    -- ^ The sub-tensor at the given index. The given shape is of the
    -- large tensor. If index is out of bounds, the result is defined and is 0.
  DeltaScatterR :: forall m n p r target.
                   SNat m -> SNat n -> SNat p
                -> IShR (p + n) -> Delta target (TKR2 (m + n) r)
                -> (IxROf target m -> IxROf target p)
                -> Delta target (TKR2 (p + n) r)
    -- ^ Build a tensor by adding up tensors of rank @n@ taken from
    -- the third argument and inserted in a zero tensor
    -- at indexes of length @p@. Indexes of length 0 insert tensors trivially,
    -- so that, e.g, @DeltaScatter1 5 (const ZR) (Replicate0R [5] d) []@ is equivalent
    -- to @5 * d@. If an index of length @p@ is out of bounds, no tensor
    -- is added at such an index (and similarly in @DeltaScatterN@).
    -- The semantics of the operation permits index out of bounds
    -- and then no tensors is added at such an index.
    -- TODO: this is a haddock for DeltaScatter1; fix.
  DeltaGatherR :: forall m n p r target.
                  SNat m -> SNat n -> SNat p
               -> IShR (m + n) -> Delta target (TKR2 (p + n) r)
               -> (IxROf target m -> IxROf target p)
               -> Delta target (TKR2 (m + n) r)
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @DeltaGather1 (const ZR) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @DeltaGatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for DeltaGather1; fix.
  DeltaAppendR :: Delta target (TKR2 (1 + n) r)
               -> Delta target (TKR2 (1 + n) r)
               -> Delta target (TKR2 (1 + n) r)
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
  DeltaSliceR :: Int -> Int -> Delta target (TKR2 (1 + n) r)
              -> Delta target (TKR2 (1 + n) r)
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
  DeltaReverseR :: Delta target (TKR2 (1 + n) r)
                -> Delta target (TKR2 (1 + n) r)
    -- ^ Reverse elements of the outermost dimension.
  DeltaTransposeR :: Permutation.PermR -> Delta target (TKR2 n r)
                  -> Delta target (TKR2 n r)
    -- ^ Transpose according to the permutation.
  DeltaReshapeR :: IShR m -> Delta target (TKR2 n r)
                -> Delta target (TKR2 m r)
    -- ^ Change the shape of the tensor to the given one.
  DeltaZipR :: Delta target (TKProduct (TKR2 n y) (TKR2 n z))
            -> Delta target (TKR2 n (TKProduct y z))
  DeltaUnzipR :: Delta target (TKR2 n (TKProduct y z))
              -> Delta target (TKProduct (TKR2 n y) (TKR2 n z))

  -- Shaped tensor operations
  DeltaCastS :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2)
             => Delta target (TKS sh r1) -> Delta target (TKS sh r2)
    -- ^ The sub-tensor at the given index.
    -- If index is out of bounds, the result is defined and is 0.
  DeltaSum0S :: Delta target (TKS2 sh r) -> Delta target (TKS2 '[] r)
  DeltaDot0S :: (GoodScalar r, Show (target (TKS sh r)))
             => target (TKS sh r) -> Delta target (TKS sh r)
             -> Delta target (TKS '[] r)
  DeltaIndexS :: forall shm shn r target.
                 ShS shn
              -> Delta target (TKS2 (shm ++ shn) r) -> IxSOf target shm
              -> Delta target (TKS2 shn r)
  DeltaScatterS :: forall shm shn shp r target.
                   ShS shm -> ShS shn -> ShS shp
                -> Delta target (TKS2 (shm ++ shn) r)
                -> (IxSOf target shm -> IxSOf target shp)
                -> Delta target (TKS2 (shp ++ shn) r)
    -- ^ Build a tensor by adding up tensors of rank @n@ taken from
    -- the third argument and inserted in a zero tensor
    -- at indexes of length @p@. Indexes of length 0 insert tensors trivially,
    -- so that, e.g, @DeltaScatter1 5 (const ZR) (Replicate0R [5] d) []@ is equivalent
    -- to @5 * d@. If an index of length @p@ is out of bounds, no tensor
    -- is added at such an index (and similarly in @DeltaScatterN@).
    -- The semantics of the operation permits index out of bounds
    -- and then no tensors is added at such an index.
    -- TODO: this is a haddock for DeltaScatter1; fix.
  DeltaGatherS :: forall shm shn shp r target.
                  ShS shm -> ShS shn -> ShS shp
               -> Delta target (TKS2 (shp ++ shn) r)
               -> (IxSOf target shm -> IxSOf target shp)
               -> Delta target (TKS2 (shm ++ shn) r)
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @DeltaGather1 (const ZR) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @DeltaGatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for DeltaGather1; fix.
  DeltaAppendS :: forall target r m n sh.
                  Delta target (TKS2 (m ': sh) r)
               -> Delta target (TKS2 (n ': sh) r)
               -> Delta target (TKS2 ((m + n) ': sh) r)
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
    -- The integer argument is the outermost size of the first array.
  DeltaSliceS :: SNat i -> SNat n -> SNat k
              -> Delta target (TKS2 (i + n + k ': sh) r)
              -> Delta target (TKS2 (n ': sh) r)
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
    -- The last argument is the outermost size of the argument array.
  DeltaReverseS :: Delta target (TKS2 (n ': sh) r)
                -> Delta target (TKS2 (n ': sh) r)
    -- ^ Reverse elements of the outermost dimension.
  DeltaTransposeS :: forall perm sh r target.
                     (PermC perm, Rank perm <= Rank sh)
                  => Permutation.Perm perm
                  -> Delta target (TKS2 sh r)
                  -> Delta target (TKS2 (Permutation.PermutePrefix perm sh) r)
    -- ^ Transpose according to the permutation.
  DeltaReshapeS :: Nested.Product sh ~ Nested.Product sh2
                => ShS sh2
                -> Delta target (TKS2 sh r)
                -> Delta target (TKS2 sh2 r)
    -- ^ Change the shape of the tensor from the first to the second.
  DeltaZipS :: Delta target (TKProduct (TKS2 sh y) (TKS2 sh z))
            -> Delta target (TKS2 sh (TKProduct y z))
  DeltaUnzipS :: Delta target (TKS2 sh (TKProduct y z))
              -> Delta target (TKProduct (TKS2 sh y) (TKS2 sh z))

  -- Mixed tensor operations
  DeltaCastX :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2)
             => Delta target (TKX sh r1) -> Delta target (TKX sh r2)
  DeltaSum0X :: Delta target (TKX2 sh r) -> Delta target (TKX2 '[] r)
  DeltaDot0X :: (GoodScalar r, Show (target (TKX sh r)))
             => target (TKX sh r) -> Delta target (TKX sh r)
             -> Delta target (TKX '[] r)
  DeltaIndexX :: forall shm shn r target.
                 StaticShX shn
              -> Delta target (TKX2 (shm ++ shn) r) -> IxXOf target shm
              -> Delta target (TKX2 shn r)
  DeltaScatterX :: StaticShX shm -> StaticShX shn -> StaticShX shp
                -> IShX (shp ++ shn) -> Delta target (TKX2 (shm ++ shn) r)
                -> (IxXOf target shm -> IxXOf target shp)
                -> Delta target (TKX2 (shp ++ shn) r)
  DeltaGatherX :: StaticShX shm -> StaticShX shn -> StaticShX shp
               -> IShX (shm ++ shn) -> Delta target (TKX2 (shp ++ shn) r)
               -> (IxXOf target shm -> IxXOf target shp)
               -> Delta target (TKX2 (shm ++ shn) r)
  DeltaAppendX :: Delta target (TKX2 (Just m ': sh) r)
               -> Delta target (TKX2 (Just n ': sh) r)
               -> Delta target (TKX2 (Just (m + n) ': sh) r)
  DeltaSliceX :: SNat i -> SNat n -> SNat k
              -> Delta target (TKX2 (Just (i + n + k) ': sh) r)
              -> Delta target (TKX2 (Just n ': sh) r)
  DeltaReverseX :: Delta target (TKX2 (mn ': sh) r)
                -> Delta target (TKX2 (mn ': sh) r)
  DeltaTransposeX :: forall perm sh r target.
                     (PermC perm, Rank perm <= Rank sh)
                  => Permutation.Perm perm
                  -> Delta target (TKX2 sh r)
                  -> Delta target (TKX2 (Permutation.PermutePrefix perm sh) r)
  DeltaReshapeX :: IShX sh2 -> Delta target (TKX2 sh r)
                -> Delta target (TKX2 sh2 r)
  DeltaZipX :: Delta target (TKProduct (TKX2 sh y) (TKX2 sh z))
            -> Delta target (TKX2 sh (TKProduct y z))
  DeltaUnzipX :: Delta target (TKX2 sh (TKProduct y z))
              -> Delta target (TKProduct (TKX2 sh y) (TKX2 sh z))

  -- Conversions
  DeltaFromS :: forall y z target.
                STensorKind z -> Delta target y -> Delta target z
  DeltaSFromK :: GoodScalar r
              => Delta target (TKScalar r) -> Delta target (TKS '[] r)
  DeltaSFromR :: forall sh r target.
                 ShS sh -> Delta target (TKR2 (Rank sh) r)
              -> Delta target (TKS2 sh r)
  DeltaSFromX :: forall sh sh' r target. Rank sh ~ Rank sh'
              => ShS sh -> Delta target (TKX2 sh' r)
              -> Delta target (TKS2 sh r)

  DeltaXNestR :: StaticShX sh1 -> SNat m
              -> Delta target (TKX2 (sh1 ++ Replicate m Nothing) x)
              -> Delta target (TKX2 sh1 (TKR2 m x))
    -- The constraints about ++ in these three are needed for deriving Show.
  DeltaXNestS :: StaticShX sh1 -> ShS sh2
              -> Delta target (TKX2 (sh1 ++ MapJust sh2) x)
              -> Delta target (TKX2 sh1 (TKS2 sh2 x))
  DeltaXNest :: StaticShX sh1 -> StaticShX sh2
             -> Delta target (TKX2 (sh1 ++ sh2) x)
             -> Delta target (TKX2 sh1 (TKX2 sh2 x))
  DeltaXUnNestR :: Delta target (TKX2 sh1 (TKR2 m x))
                -> Delta target (TKX2 (sh1 ++ Replicate m Nothing) x)
  DeltaXUnNestS :: Delta target (TKX2 sh1 (TKS2 sh2 x))
                -> Delta target (TKX2 (sh1 ++ MapJust sh2) x)
  DeltaXUnNest :: Delta target (TKX2 sh1 (TKX2 sh2 x))
               -> Delta target (TKX2 (sh1 ++ sh2) x)

deriving instance ( Show (IntOf target)
                  , (forall y7. KnownSTK y7 => Show (target y7)) )
                  => Show (Delta target y)


-- * Full tensor kind derivation for delta expressions

ftkDelta :: forall target y.
            Delta target y -> FullTensorKind y
ftkDelta = \case
  DeltaPair t1 t2 -> FTKProduct (ftkDelta t1) (ftkDelta t2)
  DeltaProject1 v -> case ftkDelta v of
    FTKProduct ftk1 _ -> ftk1
  DeltaProject2 v -> case ftkDelta v of
    FTKProduct _ ftk2 -> ftk2
  DeltaFromVector snat _ l -> case V.toList l of
    [] -> error "ftkDelta: empty vector"
    d : _ -> buildFTK snat (ftkDelta d)
  DeltaSum snat stk d -> razeFTK snat stk (ftkDelta d)
  DeltaReplicate snat _ d -> buildFTK snat (ftkDelta d)
  DeltaMapAccumR k bShs _eShs _q _es _df _rf acc0' _es'
    | Dict <- lemKnownSTKOfBuild k (ftkToSTK bShs) ->
      FTKProduct (ftkDelta acc0') (buildFTK k bShs)
  DeltaMapAccumL k bShs _eShs _q _es _df _rf acc0' _es'
    | Dict <- lemKnownSTKOfBuild k (ftkToSTK bShs) ->
      FTKProduct (ftkDelta acc0') (buildFTK k bShs)

  DeltaShare _ d -> ftkDelta d
  DeltaInput ftk _ -> ftk

  DeltaZero ftk -> ftk
  DeltaScale _ d -> ftkDelta d
  DeltaAdd d _ -> ftkDelta d

  DeltaCastK{} -> FTKScalar

  DeltaCastR d -> case ftkDelta d of
    FTKR sh _ -> FTKR sh FTKScalar
  DeltaSum0R d -> case ftkDelta d of
    FTKR _ x -> FTKR ZSR x
  DeltaDot0R{} -> FTKR ZSR FTKScalar
  DeltaIndexR SNat d ix | SNat <- ixrRank ix -> case ftkDelta d of
    FTKR sh x -> FTKR (dropShape sh) x
  DeltaScatterR _ _ _ sh d _ -> case ftkDelta d of
    FTKR _ x -> FTKR sh x
  DeltaGatherR _ _ _ sh d _ -> case ftkDelta d of
    FTKR _ x -> FTKR sh x
  DeltaAppendR a b -> case ftkDelta a of
    FTKR ZSR _ -> error "ftkDelta: impossible pattern needlessly required"
    FTKR (ai :$: ash) x -> case ftkDelta b of
      FTKR ZSR _ -> error "ftkDelta: impossible pattern needlessly required"
      FTKR (bi :$: _) _ -> FTKR (ai + bi :$: ash) x
  DeltaSliceR _ n d -> case ftkDelta d of
    FTKR sh x -> FTKR (n :$: shrTail sh) x
  DeltaReverseR d -> ftkDelta d
  DeltaTransposeR perm d -> case ftkDelta d of
    FTKR sh x -> FTKR (Nested.Internal.Shape.shrPermutePrefix perm sh) x
  DeltaReshapeR sh d -> case ftkDelta d of
    FTKR _ x -> FTKR sh x
  DeltaZipR d -> case ftkDelta d of
    FTKProduct (FTKR sh y) (FTKR _ z) -> FTKR sh (FTKProduct y z)
  DeltaUnzipR d -> case ftkDelta d of
    FTKR sh (FTKProduct y z) -> FTKProduct (FTKR sh y) (FTKR sh z)

  DeltaCastS d -> case ftkDelta d of
    FTKS sh FTKScalar -> FTKS sh FTKScalar
  DeltaSum0S d -> case ftkDelta d of
    FTKS _ x -> FTKS ZSS x
  DeltaDot0S{} -> FTKS ZSS FTKScalar
  DeltaIndexS shn d _ix -> case ftkDelta d of
    FTKS _ x -> FTKS shn x
  DeltaScatterS _shm shn shp d _ -> case ftkDelta d of
    FTKS _ x -> FTKS (shp `shsAppend` shn) x
  DeltaGatherS shm shn _shp d _ -> case ftkDelta d of
    FTKS _ x -> FTKS (shm `shsAppend` shn) x
  DeltaAppendS a b -> case (ftkDelta a, ftkDelta b) of
    (FTKS (m :$$ sh) x, FTKS (n :$$ _) _) -> FTKS (snatPlus m n :$$ sh) x
  DeltaSliceS _ n@SNat _ d -> case ftkDelta d of
    FTKS (_ :$$ sh) x -> FTKS (n :$$ sh) x
  DeltaReverseS d -> ftkDelta d
  DeltaTransposeS perm d -> case ftkDelta d of
    FTKS sh x -> FTKS (shsPermutePrefix perm sh) x
  DeltaReshapeS sh2 d -> case ftkDelta d of
    FTKS _ x -> FTKS sh2 x
  DeltaZipS d -> case ftkDelta d of
    FTKProduct (FTKS sh y) (FTKS _ z) -> FTKS sh (FTKProduct y z)
  DeltaUnzipS d -> case ftkDelta d of
    FTKS sh (FTKProduct y z) -> FTKProduct (FTKS sh y) (FTKS sh z)

  DeltaCastX d -> case ftkDelta d of
    FTKX sh FTKScalar -> FTKX sh FTKScalar
  DeltaSum0X d -> case ftkDelta d of
    FTKX _ x -> FTKX ZSX x
  DeltaDot0X{} -> FTKX ZSX FTKScalar
  DeltaIndexX @shm @shn shn d ix -> case ftkDelta d of
    FTKX sh x | SNat @len <- ixxRank ix ->
      gcastWith (unsafeCoerceRefl :: Drop (Rank shm) (shm ++ shn) :~: shn) $
      withKnownShX (ssxFromShape sh) $
      withKnownShX shn $
      FTKX (dropShX @len sh) x  -- TODO: (shxDropSSX sh (ixxToSSX ix)) x
  DeltaScatterX _ _ _ sh d _ -> case ftkDelta d of
    FTKX _ x -> FTKX sh x
  DeltaGatherX _ _ _ sh d _ -> case ftkDelta d of
    FTKX _ x -> FTKX sh x
  DeltaAppendX a b -> case (ftkDelta a, ftkDelta b) of
    (FTKX (Nested.SKnown m :$% sh) x, FTKX (Nested.SKnown n :$% _) _) ->
      FTKX (Nested.SKnown (snatPlus m n) :$% sh) x
  DeltaSliceX _ n@SNat _ d -> case ftkDelta d of
    FTKX (_ :$% sh) x -> FTKX (Nested.SKnown n :$% sh) x
  DeltaReverseX d -> ftkDelta d
  DeltaTransposeX perm d -> case ftkDelta d of
    FTKX sh x -> FTKX (shxPermutePrefix perm sh) x
  DeltaReshapeX sh2 d -> case ftkDelta d of
    FTKX _ x -> FTKX sh2 x
  DeltaZipX d -> case ftkDelta d of
    FTKProduct (FTKX sh y) (FTKX _ z) -> FTKX sh (FTKProduct y z)
  DeltaUnzipX d -> case ftkDelta d of
    FTKX sh (FTKProduct y z) -> FTKProduct (FTKX sh y) (FTKX sh z)

  DeltaFromS stk0 d ->
    let fromS :: FullTensorKind y2 -> STensorKind z2 -> FullTensorKind z2
        fromS ftk stk = case (ftk, stk) of
          _ | Just Refl <- sameSTK (ftkToSTK ftk) stk -> ftk
          (FTKS ZSS (FTKScalar @r1), STKScalar @r2) ->
            case testEquality (typeRep @r1) (typeRep @r2) of
              Just Refl -> FTKScalar
              Nothing -> error "ftkDelta: wrong tensor kinds for DeltaFromS"
          (FTKS sh x, STKR nx zx) ->
            case ( sameSTK (ftkToSTK x) zx
                 , testEquality (shsRank sh) nx ) of
              (Just Refl, Just Refl) -> FTKR (shCastSR sh) x
              _ -> error $ "ftkDelta: wrong tensor kinds for DeltaFromS: "
                           ++ show (ftkToSTK x) ++ " vs " ++ show zx ++ " and "
                           ++ show sh ++ " vs " ++ show nx
          (FTKS sh x, STKX shx zx) ->
            case ( sameSTK (ftkToSTK x) zx
                 , testEquality (shsRank sh) (ssxRank shx) ) of
              (Just Refl, Just Refl) -> FTKX (shCastSX shx sh) x
              _ -> error "ftkDelta: wrong tensor kinds for DeltaFromS"
          (FTKProduct ftk1 ftk2, STKProduct stk1 stk2) ->
            FTKProduct (fromS ftk1 stk1) (fromS ftk2 stk2)
          _ -> error "ftkDelta: wrong tensor kinds for DeltaFromS"
    in fromS (ftkDelta d) stk0
  DeltaSFromK{} -> FTKS ZSS FTKScalar
  DeltaSFromR sh d -> case ftkDelta d of
    FTKR _ x -> FTKS sh x
  DeltaSFromX sh d -> case ftkDelta d of
    FTKX _ x -> FTKS sh x

  DeltaXNestR sh1 (SNat @m) d -> case ftkDelta d of
    FTKX sh x -> FTKX (shxTakeSSX (Proxy @(Replicate m Nothing)) sh sh1)
                      (FTKR (shCvtXR' (shxDropSSX sh sh1)) x)
  DeltaXNestS @_ @sh2 sh1 sh2 d -> case ftkDelta d of
    FTKX sh x -> FTKX (shxTakeSSX (Proxy @(MapJust sh2)) sh sh1)
                                  (FTKS sh2 x)
  DeltaXNest @_ @sh2 sh1 _sh2 d -> case ftkDelta d of
    FTKX sh x -> FTKX (shxTakeSSX (Proxy @sh2) sh sh1)
                      (FTKX (shxDropSSX sh sh1) x)
  DeltaXUnNestR d -> case ftkDelta d of
    FTKX sh1 (FTKR sh2 x) -> FTKX (sh1 `shxAppend` shCvtRX sh2) x
  DeltaXUnNestS d -> case ftkDelta d of
    FTKX sh1 (FTKS sh2 x) -> FTKX (sh1 `shxAppend` shCvtSX sh2) x
  DeltaXUnNest d -> case ftkDelta d of
    FTKX sh1 (FTKX sh2 x) -> FTKX (sh1 `shxAppend` sh2) x
