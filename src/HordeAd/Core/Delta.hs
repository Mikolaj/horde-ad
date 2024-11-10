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
  ( -- * Delta expression evaluation
    gradientFromDelta, derivativeFromDelta
    -- * Abstract syntax trees of the delta expressions
  , Delta(..)
    -- * Delta expression identifiers
  , NodeId (..), InputId, toInputId
    -- * Exported to be specialized elsewhere
  , evalFromnMap, EvalState
  ) where

import Prelude

import Control.Arrow (second)
import Control.Exception.Assert.Sugar
import Data.Array.Internal (valueOf)
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.Kind (Type)
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Some
import Data.Strict.Vector qualified as Data.Vector
import Data.Traversable (mapAccumL)
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, sameNat, type (+), type (<=))
import Text.Show (showListWith)
import Text.Show.Functions ()
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (pattern (:.%), pattern ZIX)
import Data.Array.Nested (KnownShX, Rank, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (shrRank)
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.ShapedList
  (Drop, IndexSh, IndexShX, Take, pattern (:.$), pattern ZIS)
import HordeAd.Util.SizedList

type IMap target = DEnumMap (InputId target) (RepM target)

type ADMap target = DEnumMap (NodeId target) (RepAD target)

gradientFromDelta
  :: forall x z target.
     (ADReadyNoLet target, ShareTensor target, TensorKind z)
  => TensorKindFull x
  -> target z
  -> Maybe (target (ADTensorKind z))
  -> Delta target z
  -> target (ADTensorKind x)
gradientFromDelta !parameters0 value !mdt deltaTopLevel =
  let oneAtF = repConstant 1 $ aDTensorKind $ tshapeFull (stensorKind @z) value
      dt = fromMaybe oneAtF mdt
      s0 = initEvalState parameters0
      s1 = evalR s0 dt deltaTopLevel
      s2 = evalFromnMap s1
      rebuildInputs :: forall ady.  -- ady ~ ADTensorKind y
                       [Some (RepM target)] -> TensorKindFull ady
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
        FTKR @r @n sh | SNat <- shrRank sh -> case els of
          Some mt@(MTKR @r2 @n2 t) : rest ->
            case ( sameNat (Proxy @n) (Proxy @n2)
                 , testEquality (typeRep @r) (typeRep @r2) ) of
              (Just Refl, Just Refl) -> (t, rest)
              _ -> error $ "gradientFromDelta: wrong type: " ++ show mt
                           ++ " instead of "
                           ++ "FTKR @" ++ show (typeRep @r)
                           ++ " @" ++ show (valueOf @n :: Int)
                           ++ " within " ++ show_iMap (iMap s2)
          Some mt@(MTKRDummy @r2 @sh2) : rest
            | Dict <- lemKnownNatRank (knownShS @sh2)
            , Just Refl <- sameNat (Proxy @n) (Proxy @(Rank sh2))
            , Just Refl <- testEquality (typeRep @r) (typeRep @r2) ->
              (evalRepM mt, rest)
          _ -> error $ "gradientFromDelta: illegal RepM: "
                       ++ show_iMap (iMap s2)
        FTKS @r @sh sh -> withKnownShS sh $ case els of
          Some mt@(MTKS @r2 @sh2 t) : rest ->
            case ( sameShape @sh @sh2
                 , testEquality (typeRep @r) (typeRep @r2) ) of
              (Just Refl, Just Refl) -> (t, rest)
              _ -> error $ "gradientFromDelta: wrong type: " ++ show mt
                           ++ " instead of "
                           ++ "FTKS @" ++ show (typeRep @r)
                           ++ " @" ++ show (shapeT @sh)
                           ++ " within " ++ show_iMap (iMap s2)
          Some mt@(MTKSDummy @r2 @sh2) : rest
            | Just Refl <- sameShape @sh @sh2
            , Just Refl <- testEquality (typeRep @r) (typeRep @r2) ->
              (evalRepM mt, rest)
          _ -> error $ "gradientFromDelta: illegal RepM: "
                       ++ show_iMap (iMap s2)
        FTKX{} -> error "TODO"
        FTKProduct @y1 @y2 ftk1 ftk2 | Dict <- lemTensorKindOfF ftk1
                                     , Dict <- lemTensorKindOfF ftk2 ->
            let (t1, rest1) = rebuildInputs @y1 els ftk1
                (t2, rest2) = rebuildInputs @y2 rest1 ftk2
            in (tpair t1 t2, rest2)
        FTKUntyped shs ->
          let toDynamicTensor :: Some (RepM target)
                              -> DynamicTensor target
              toDynamicTensor (Some b) = case b of
                MTKScalar @r t -> DynamicRanked @r @0 $ runRepScalar t
                MTKR @r @n t -> DynamicRanked @r @n t
                MTKS @r @sh t -> DynamicShaped @r @sh t
                MTKScalarDummy @r -> DynamicRankedDummy @r @'[] Proxy Proxy
                MTKRDummy @r @sh -> DynamicRankedDummy @r @sh Proxy Proxy
                MTKSDummy @r @sh -> DynamicShapedDummy @r @sh Proxy Proxy
              len = V.length shs
              (els1, els2) = splitAt len els
          in ( dmkHVector
               $ V.fromList $ map toDynamicTensor els1
             , els2 )
      (res, remainder) = rebuildInputs @(ADTensorKind x) (DMap.elems $ iMap s2)
                         $ aDTensorKind parameters0
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
      generateDSums :: Int -> TensorKindFull y -> target y
                    -> ( [DSum (InputId target) (RepM target)]
                       , Int )
      generateDSums j ftk t = case ftk of
        FTKScalar @r -> ([InputId j :=> MTKScalar @r t], j + 1)
        FTKR @r sh | SNat <- shrRank sh ->
          withShapeP (shapeToList sh) $ \(Proxy @sh) ->
            case lemKnownNatRank (knownShS @sh) of
              Dict -> ([InputId j :=> MTKR @r t], j + 1)
        FTKS @r @sh sh -> withKnownShS sh
                          $ ([InputId j :=> MTKS @r @sh t], j + 1)
        FTKX{} -> error "TODO"
        FTKProduct ftk1 ftk2 | Dict <- lemTensorKindOfF ftk1
                             , Dict <- lemTensorKindOfF ftk2 ->
          let (t1, t2) = tunpair t
              (ds1, j1) = generateDSums j ftk1 t1
              (ds2, j2) = generateDSums j1 ftk2 t2
          in (ds1 ++ ds2, j2)
        FTKUntyped{} ->
          let ts = tunvector t
              len = V.length ts
          in ( zipWith dynamicTensorToRepM [j ..] $ V.toList ts
             , j + len )
      iMap = DMap.fromDistinctAscList $ fst
             $ generateDSums 0 (tshapeFull stensorKind ds) ds
      s0 = DMap.empty
      !(!_s2, !c) = fwdR iMap s0 deltaTopLevel
  in c

evalRepM :: forall target x. ADReadyNoLet target
         => RepM target x -> target x
evalRepM = \case
  MTKScalar t -> t
  MTKR t -> t
  MTKS t -> t
  MTKScalarDummy -> rmkRepScalar $ rscalar 0
  MTKRDummy @_ @sh -> withListSh (Proxy @sh) $ \sh4 -> rzero sh4
  MTKSDummy -> srepl 0

dynamicTensorToRepM
  :: Int -> DynamicTensor target
  -> DSum (InputId target) (RepM target)
dynamicTensorToRepM n = \case
  DynamicRanked t -> InputId n :=> MTKR t
  DynamicShaped t -> InputId n :=> MTKS t
  DynamicRankedDummy{} ->
    error "dynamicTensorToRepM: unexpected DynamicRankedDummy"
  DynamicShapedDummy{} ->
    error "dynamicTensorToRepM: unexpected DynamicShapedDummy"

repToM
  :: STensorKindType x -> target x
  -> RepM target x
repToM stk t = case stk of
  STKScalar _ -> MTKScalar t
  STKR STKScalar{} SNat -> MTKR t
  STKS STKScalar{} sh -> withKnownShS sh $ MTKS t
  STKX{} -> error "repToM"
  STKProduct{} -> error "repToM"
  STKUntyped{} -> error "repToM"
  _ -> error "TODO"

addRepM ::
  ADReadyNoLet target
  => RepM target y
  -> RepM target y
  -> RepM target y
addRepM a b = case (a, b) of
  (MTKScalar ta, MTKScalar tb) ->
    MTKScalar $ rmkRepScalar $ runRepScalar ta + runRepScalar tb
  (MTKR ta, MTKR tb) -> MTKR $ ta + tb
  (MTKScalarDummy, _) -> b
  (_, MTKScalarDummy) -> a
  (MTKRDummy, _) -> b
  (_, MTKRDummy) -> a
  (MTKS ta, MTKS tb) -> MTKS $ ta + tb
  (MTKSDummy, _) -> b
  (_, MTKSDummy) -> a

-- This is very similar to DynamicTensor, but the second type parameter
-- gives a peek of what's inside, which is crucial for dependent maps
-- as opposed to existential vectors.
type role RepM nominal nominal
data RepM target y where
  MTKScalar :: GoodScalar r
            => target (TKScalar r)
            -> RepM target (TKScalar r)
  MTKR :: (GoodScalar r, KnownNat n)
       => target (TKR r n)
       -> RepM target (TKR r n)
  MTKS :: (GoodScalar r, KnownShS sh)
       => target (TKS r sh)
       -> RepM target (TKS r sh)
  MTKScalarDummy :: GoodScalar r
                 => RepM target (TKScalar r)
  MTKRDummy :: (GoodScalar r, KnownShS sh)
            => RepM target (TKR r (Rank sh))
  MTKSDummy  :: (GoodScalar r, KnownShS sh)
             => RepM target (TKS r sh)

deriving instance ( CRanked target Show
                  , Show (target TKUntyped)
                  , TensorKind y )
                  => Show (RepM target y)

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
-- The `NodeId` identifier that appears in a @ShareG n d@ expression
-- is the unique identity stamp of subterm @d@, that is, there is
-- no different term @e@ such that @ShareG n e@ appears in any delta
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

type role Delta nominal nominal
data Delta :: Target -> TensorKindType -> Type where
  ScalarG :: GoodScalar r
          => Delta target (TKScalar r) -> Delta target (TKR r 0)
  UnScalarG :: GoodScalar r
            => Delta target (TKR r 0) -> Delta target (TKScalar r)
  PairG :: (TensorKind y, TensorKind z)
         => Delta target y -> Delta target z
         -> Delta target (TKProduct y z)
  Project1G :: forall x z target. TensorKind z
            => Delta target (TKProduct x z) -> Delta target x
  Project2G :: forall x z target. TensorKind x
            => Delta target (TKProduct x z) -> Delta target z
  InputG :: forall target y.
            TensorKindFull y -> InputId target y -> Delta target y
  ShareG :: NodeId target y -> Delta target y -> Delta target y
  ZeroG :: TensorKindFull y -> Delta target y
  ScaleG :: Num (target y)
         => target y -> Delta target y -> Delta target y
  AddG :: Num (target y)
       => Delta target y -> Delta target y -> Delta target y

  IndexR :: (GoodScalar r, KnownNat n, KnownNat m)
         => Delta target (TKR r (m + n)) -> IndexOf target m
         -> Delta target (TKR r n)
    -- ^ The sub-tensor at the given index. The given shape is of the
    -- large tensor. If index is out of bounds, the result is defined and is 0.
  SumR :: (GoodScalar r, KnownNat n)
       => Delta target (TKR r (1 + n)) -> Delta target (TKR r n)
  Sum0R :: (GoodScalar r, KnownNat n)
        => Delta target (TKR r n) -> Delta target (TKR r 0)
  Dot0R :: (KnownNat n, GoodScalar r)
        => target (TKR r n) -> Delta target (TKR r n) -> Delta target (TKR r 0)
  ScatterR :: (GoodScalar r, KnownNat m, KnownNat p, KnownNat n)
           => IShR (p + n) -> Delta target (TKR r (m + n))
           -> (IndexOf target m -> IndexOf target p)
           -> Delta target (TKR r (p + n))
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
              => Data.Vector.Vector (Delta target (TKR r n))
              -> Delta target (TKR r (1 + n))
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  ReplicateR :: (GoodScalar r, KnownNat n)
             => Int -> Delta target (TKR r n)
             -> Delta target (TKR r (1 + n))
    -- ^ Copy the given tensor along the new, outermost dimension.
  AppendR :: (GoodScalar r, KnownNat n)
          => Delta target (TKR r (1 + n))
          -> Delta target (TKR r (1 + n))
          -> Delta target (TKR r (1 + n))
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
  SliceR :: (GoodScalar r, KnownNat n)
         => Int -> Int -> Delta target (TKR r (1 + n))
         -> Delta target (TKR r (1 + n))
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
  ReverseR :: (GoodScalar r, KnownNat n)
           => Delta target (TKR r (1 + n)) -> Delta target (TKR r (1 + n))
    -- ^ Reverse elements of the outermost dimension.
  TransposeR :: (GoodScalar r, KnownNat n)
             => Permutation.PermR -> Delta target (TKR r n)
             -> Delta target (TKR r n)
    -- ^ Transpose according to the permutation.
  ReshapeR :: (GoodScalar r, KnownNat n, KnownNat m)
           => IShR m -> Delta target (TKR r n)
           -> Delta target (TKR r m)
    -- ^ Change the shape of the tensor to the given one.
  GatherR :: (GoodScalar r, KnownNat m, KnownNat p, KnownNat n)
          => IShR (m + n) -> Delta target (TKR r (p + n))
          -> (IndexOf target m -> IndexOf target p)
          -> Delta target (TKR r (m + n))
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @Gather1 (const ZR) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @GatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for Gather1; fix.
  CastR :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2, KnownNat n)
        => Delta target (TKR r1 n) -> Delta target (TKR r2 n)
  RFromS :: forall sh r target. (GoodScalar r, KnownShS sh)
         => Delta target (TKS r sh)
         -> Delta target (TKR r (Rank sh))
  RFromH :: (GoodScalar r, KnownNat n)
         => Delta target TKUntyped -> Int -> Delta target (TKR r n)

  IndexS :: (KnownShS sh1, KnownShS sh2, KnownShS (sh1 ++ sh2), GoodScalar r)
         => Delta target (TKS r (sh1 ++ sh2))
         -> IndexSh target sh1
         -> Delta target (TKS r sh2)
    -- ^ The sub-tensor at the given index.
    -- If index is out of bounds, the result is defined and is 0.
  SumS :: (GoodScalar r, KnownNat n, KnownShS sh)
       => Delta target (TKS r (n ': sh)) -> Delta target (TKS r sh)
  Sum0S :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
        => Delta target (TKS r sh) -> Delta target (TKS r '[])
  Dot0S :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
        => target (TKS r sh) -> Delta target (TKS r sh)
        -> Delta target (TKS r '[])
  ScatterS :: forall target r sh2 p sh.
              ( GoodScalar r, KnownShS sh2, KnownShS sh, KnownNat p
              , KnownShS (Take p sh), KnownShS (Drop p sh)
              , KnownShS (sh2 ++ Drop p sh) )
           => Delta target (TKS r (sh2 ++ Drop p sh))
           -> (IndexSh target sh2
               -> IndexSh target (Take p sh))
           -> Delta target (TKS r sh)
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
              => Data.Vector.Vector (Delta target (TKS r sh))
              -> Delta target (TKS r (n ': sh))
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  ReplicateS :: forall target r n sh.
                (GoodScalar r, KnownShS sh, KnownNat n)
             => Delta target (TKS r sh) -> Delta target (TKS r (n ': sh))
    -- ^ Copy the given tensor along the new, outermost dimension.
  AppendS :: forall target r m n sh.
             (GoodScalar r, KnownNat m, KnownNat n, KnownShS sh)
          => Delta target (TKS r (m ': sh))
          -> Delta target (TKS r (n ': sh))
          -> Delta target (TKS r ((m + n) ': sh))
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
    -- The integer argument is the outermost size of the first array.
  SliceS :: forall target i n k r sh.
            (GoodScalar r, KnownNat i, KnownNat n, KnownNat k, KnownShS sh)
         => Delta target (TKS r (i + n + k ': sh))
         -> Delta target (TKS r (n ': sh))
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
    -- The last argument is the outermost size of the argument array.
  ReverseS :: (GoodScalar r, KnownShS sh, KnownNat n)
           => Delta target (TKS r (n ': sh))
           -> Delta target (TKS r (n ': sh))
    -- ^ Reverse elements of the outermost dimension.
  TransposeS :: forall perm sh r target.
                (GoodScalar r, PermC perm, KnownShS sh, Rank perm <= Rank sh)
             => Permutation.Perm perm
             -> Delta target (TKS r sh)
             -> Delta target (TKS r (Permutation.PermutePrefix perm sh))
    -- ^ Transpose according to the permutation.
  ReshapeS :: ( GoodScalar r, KnownShS sh, KnownShS sh2
              , Nested.Product sh
                ~ Nested.Product sh2 )
           => Delta target (TKS r sh)
           -> Delta target (TKS r sh2)
    -- ^ Change the shape of the tensor from the first to the second.
  GatherS :: forall target r sh2 p sh.
             ( GoodScalar r, KnownShS sh2, KnownShS sh, KnownNat p
             , KnownShS (Take p sh), KnownShS (Drop p sh)
             , KnownShS (sh2 ++ Drop p sh) )
          => Delta target (TKS r sh)
          -> (IndexSh target sh2
              -> IndexSh target (Take p sh))
          -> Delta target (TKS r (sh2 ++ Drop p sh))
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @Gather1 (const ZR) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @GatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for Gather1; fix.
  CastS :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2, KnownShS sh)
        => Delta target (TKS r1 sh) -> Delta target (TKS r2 sh)
  SFromR :: forall sh r target. (GoodScalar r, KnownShS sh, KnownNat (Rank sh))
         => Delta target (TKR r (Rank sh))
         -> Delta target (TKS r sh)
  SFromH :: (GoodScalar r, KnownShS sh)
         => Delta target TKUntyped -> Int -> Delta target (TKS r sh)

  IndexX :: (KnownShX sh1, KnownShX sh2, KnownShX (sh1 ++ sh2), GoodScalar r)
         => Delta target (TKX r (sh1 ++ sh2))
         -> IndexShX target sh1
         -> Delta target (TKX r sh2)
  FromVectorX :: (GoodScalar r, KnownShX sh, KnownNat n)
              => Data.Vector.Vector (Delta target (TKX r sh))
              -> Delta target (TKX r (Just n ': sh))

  HToH :: HVector (Delta target) -> Delta target TKUntyped
  MapAccumR
    :: forall target k accShs bShs eShs.
       ( TensorKind accShs, TensorKind bShs, TensorKind eShs
       , TensorKind (BuildTensorKind k eShs)
       , TensorKind (BuildTensorKind k accShs) )
    => SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
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
  MapAccumL
    :: forall target k accShs bShs eShs.
       ( TensorKind accShs, TensorKind bShs, TensorKind eShs
       , TensorKind (BuildTensorKind k eShs)
       , TensorKind (BuildTensorKind k accShs) )
    => SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
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

deriving instance ( TensorKind y
                  , Show (target TKUntyped)
                  , Show (IntOf target)
                  , CRanked target Show )
                  => Show (Delta target y)

shapeDeltaFull :: forall target y. TensorKind y
               => Delta target y -> TensorKindFull y
shapeDeltaFull = \case
  ScalarG{} -> FTKR ZSR
  UnScalarG{} -> FTKScalar
  PairG t1 t2 -> FTKProduct (shapeDeltaFull t1) (shapeDeltaFull t2)
  Project1G v -> case shapeDeltaFull v of
    FTKProduct ftk1 _ -> ftk1
  Project2G v -> case shapeDeltaFull v of
    FTKProduct _ ftk2 -> ftk2
  InputG ftk _ -> ftk
  ShareG _ d -> shapeDeltaFull d
  ZeroG ftk -> ftk
  ScaleG _ d -> shapeDeltaFull d
  AddG d _ -> shapeDeltaFull d

  IndexR d _ -> FTKR $ dropShape (shapeDelta d)
  SumR d -> FTKR $ tailShape (shapeDelta d)
  Sum0R{} -> FTKR ZSR
  Dot0R{} -> FTKR ZSR
  ScatterR sh _ _ -> FTKR sh
  FromVectorR l -> case V.toList l of
    [] -> case stensorKind @y of
      STKR @_ @n _ SNat -> case sameNat (Proxy @n) (Proxy @1) of
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

  IndexS{} -> FTKS knownShS
  SumS{} -> FTKS knownShS
  Sum0S{} -> FTKS knownShS
  Dot0S{} -> FTKS knownShS
  ScatterS{} -> FTKS knownShS
  FromVectorS{} -> FTKS knownShS
  ReplicateS{} -> FTKS knownShS
  AppendS{} -> FTKS knownShS
  SliceS{} -> FTKS knownShS
  ReverseS{} -> FTKS knownShS
  TransposeS @perm @sh2 perm _v ->
    withShapeP
      (permutePrefixList (Permutation.permToList' perm)
                         (shapeT @sh2)) $ \(Proxy @sh2Perm) ->
        gcastWith (unsafeCoerce Refl :: sh2Perm :~: Permutation.PermutePrefix perm sh2) $
        FTKS knownShS
  ReshapeS{} -> FTKS knownShS
  GatherS{} -> FTKS knownShS
  CastS{} -> FTKS knownShS
  SFromR{} -> FTKS knownShS
  SFromH{} -> FTKS knownShS

  IndexX{} -> error "TODO"
  FromVectorX{} -> error "TODO"

  HToH v ->
    FTKUntyped $ V.map (voidFromDynamicF (shapeToList . shapeDelta)) v
  MapAccumR @_ @_ @_ @bShs k accShs bShs _eShs _q _es _df _rf _acc0' _es'
    | Dict <- lemTensorKindOfBuild k (stensorKind @bShs) ->
      FTKProduct accShs (buildTensorKindFull k bShs)
  MapAccumL @_ @_ @_ @bShs k accShs bShs _eShs _q _es _df _rf _acc0' _es'
    | Dict <- lemTensorKindOfBuild k (stensorKind @bShs) ->
      FTKProduct accShs (buildTensorKindFull k bShs)

shapeDelta :: forall target r n.
              (GoodScalar r, KnownNat n)
           => Delta target (TKR r n) -> IShR n
shapeDelta t = case shapeDeltaFull t of
  FTKR sh -> sh

lengthDelta :: forall target r n.
               (GoodScalar r, KnownNat n)
            => Delta target (TKR r (1 + n)) -> Int
lengthDelta d = case shapeDelta d of
  ZSR -> error "lengthDelta: impossible pattern needlessly required"
  k :$: _ -> k

shapeDeltaH :: forall target.
               Delta target TKUntyped -> VoidHVector
shapeDeltaH t = case shapeDeltaFull t of
  FTKUntyped shs -> shs


-- * Delta expression identifiers and evaluation state

type role NodeId nominal nominal
data NodeId :: Target -> TensorKindType -> Type where
  NodeId :: forall target y. TensorKind y => Int -> NodeId target y

instance Show (NodeId target y) where
  showsPrec d (NodeId n) =
    showsPrec d n  -- less verbose, more readable

  -- No Eq instance to limit hacks outside this module.
instance DMap.Enum1 (NodeId target) where
  type Enum1Info (NodeId target) = Some (Dict TensorKind)
  fromEnum1 (NodeId @_ @a n) = (n, Some @_ @a Dict)
  toEnum1 n (Some @_ @a Dict) = Some $ NodeId @target @a n

type role InputId nominal nominal
data InputId :: Target -> TensorKindType -> Type where
  InputId :: forall target y. TensorKind y => Int -> InputId target y

deriving instance Show (InputId target y)

instance DMap.Enum1 (InputId target) where
  type Enum1Info (InputId target) = Some (Dict TensorKind)
  fromEnum1 (InputId @_ @a n) = (n, Some @_ @a Dict)
  toEnum1 n (Some @_ @a Dict) = Some $ InputId @target @a n

-- | Wrap non-negative (only!) integers in the `InputId` newtype.
toInputId :: TensorKind y => Int -> InputId f y
toInputId i = assert (i >= 0) $ InputId i

tensorKindFromInputId :: InputId f y -> Dict TensorKind y
tensorKindFromInputId InputId{} = Dict

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

type role RepAD nominal nominal
newtype RepAD target y =
  RepAD {unRepAD :: target (ADTensorKind y)}

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
  :: TensorKindFull x -> EvalState target
initEvalState ftk0 =
  let -- Matches generateDeltaInputs.
      generateDSums :: Int -> TensorKindFull y
                    -> ([DSum (InputId target) (RepM target)], Int)
      generateDSums j ftk  = case ftk of
        FTKScalar @r -> ([InputId j :=> MTKScalarDummy @r], j + 1)
        FTKR @r sh -> withShapeP (shapeToList sh) $ \(Proxy @sh) ->
          case lemKnownNatRank (knownShS @sh) of
            Dict -> ([InputId j :=> MTKRDummy @r @sh], j + 1)
        FTKS @r @sh sh -> withKnownShS sh
                          $ ([InputId j :=> MTKSDummy @r @sh], j + 1)
        FTKX{} -> error "TODO"
        FTKProduct ftk1 ftk2 ->
          let (ds1, j1) = generateDSums j ftk1
              (ds2, j2) = generateDSums j1 ftk2
          in (ds1 ++ ds2, j2)
        FTKUntyped shs ->
          let len = V.length shs
          in ( zipWith fromDynamicTensor [j ..]
               $ map dynamicFromVoid $ V.toList shs
             , j + len )
      -- Create finite maps that hold values associated with inputs
      -- and with (possibly shared) term tree nodes.
      -- The former are usually initialized with dummy values so that it's cheap
      -- to check if any update has already been performed to a cell
      -- (allocating big vectors filled with zeros is too costly,
      -- especially if never used in an iteration, and adding to such vectors
      -- and especially using them as cotangent accumulators is wasteful.
      -- We take care to keep the scalar type of the dummy correct,
      -- but a shape is not preserved in a dummy, so it's not shape-correct.
      fromDynamicTensor
        :: forall target.
           Int -> DynamicTensor target
        -> DSum (InputId target) (RepM target)
      fromDynamicTensor n b = case b of
        DynamicRanked{} -> error "fromDynamicTensor: impossible case"
        DynamicShaped{} -> error "fromDynamicTensor: impossible case"
        DynamicRankedDummy @r @sh _ _ | Dict <- lemKnownNatRank (knownShS @sh) ->
          InputId n :=> MTKRDummy @r @sh
        DynamicShapedDummy @r @sh _ _ ->
          InputId n :=> MTKSDummy @r @sh
      iMap = DMap.fromDistinctAscList $ fst $ generateDSums 0
             $ aDTensorKind ftk0
      dMap = DMap.empty
      nMap = DMap.empty
  in EvalState {..}


-- * Reverse pass, transpose/evaluation of the delta expressions

-- The first argument is the evaluation state being modified,
-- the second is the cotangent accumulator that will become an actual
-- cotangent contribution when complete (see below for an explanation)
-- and the third argument is the node to evaluate.
evalRRuntimeSpecialized
  :: forall n r target.
     (GoodScalar r, KnownNat n, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind (TKR r n))
  -> Delta target (TKR r n)
  -> EvalState target
evalRRuntimeSpecialized !s !c =
  -- We dispatch on all expected underyling scalar types, which is
  -- necessary to run the correct specialization when unpacking
  -- an existential type. All IfDifferentiable and RowSum instances should
  -- be included in the list of expected underlying scalar types.
  -- If the scalar type is not on the list, performance suffers greatly.
  -- TODO: can I pattern match on (typeRep @r) instead?
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalSame @(TKR Double n) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalSame @(TKR Float n) s c
      _ -> const s

evalSRuntimeSpecialized
  :: forall sh r target.
     (GoodScalar r, KnownShS sh, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind (TKS r sh))
  -> Delta target (TKS r sh)
  -> EvalState target
evalSRuntimeSpecialized !s !c =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalSame @(TKS Double sh) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalSame @(TKS Float sh) s c
      _ -> const s

evalR
  :: forall y target.
     (TensorKind y, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalR !s !c d0 = case d0 of
  -- All constructors that admit a TKProduct kind need to be handled in evalR
  -- except for InputG that is always constructed only in basic kinds.
  PairG @y1 @y2 d1 d2 | Dict <- lemTensorKindOfAD (stensorKind @y1)
                      , Dict <- lemTensorKindOfAD (stensorKind @y2) ->
    let (c1, c2) = tunpair c
    in evalR (evalR s c1 d1) c2 d2
  Project1G @_ @z d | Dict <- lemTensorKindOfAD (stensorKind @y)
                    , Dict <- lemTensorKindOfAD (stensorKind @z) ->
    case shapeDeltaFull d of
      FTKProduct _ ftk2 ->
        let zero = repConstant 0 $ aDTensorKind ftk2
        in evalR s (tpair c zero) d
    -- if y is, e.g., TKR Int 0, we eval this delta even though we could ignore it
    -- at the price of complicating or duplicating the code slightly more
  Project2G @x d | Dict <- lemTensorKindOfAD (stensorKind @y)
                 , Dict <- lemTensorKindOfAD (stensorKind @x) ->
    case shapeDeltaFull d of
      FTKProduct ftk1 _ ->
        let zero = repConstant 0 $ aDTensorKind ftk1
        in evalR s (tpair zero c) d
  ShareG n d | Dict <- lemTensorKindOfAD (stensorKind @y) ->
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
    -- corresponding to the shared term @ShareG n d@. This total
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
              ZeroG{} -> False
              ShareG{} -> False  -- wasteful and nonsensical
              _ -> True)
    $ case DMap.lookup n $ nMap s of
        Just _ ->
          let addc x = RepAD $ taddShare stensorKind c (unRepAD x)
          in s {dMap = DMap.adjust addc n $ dMap s}
        Nothing ->
          let cd = RepAD c
          in s { nMap = DMap.insert n d $ nMap s
               , dMap = DMap.insert n cd $ dMap s }
  MapAccumR @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            _df rf acc0' es'
   | Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind bShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Just Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Just Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDTensorKind accShs
        bShsAD = aDTensorKind bShs
        eShsAD = aDTensorKind eShs
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
        s2 = evalR s dacc acc0'
    in evalR s2 des es'
  MapAccumL @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            _df rf acc0' es'
   | Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind bShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Just Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Just Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDTensorKind accShs
        bShsAD = aDTensorKind bShs
        eShsAD = aDTensorKind eShs
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
        s2 = evalR s dacc acc0'
    in evalR s2 des es'

  _ | Dict <- lemTensorKindOfAD (stensorKind @y) ->
      case sameTensorKind @y @(ADTensorKind y) of
        Just Refl -> evalSame s c d0
        _ -> s  -- the constructors remaining here have y that is a non-TKProduct
                -- so if y is equal to ADTensorKind y, the latter has
                -- the () scalar type and so no influence on the derivative.

evalSame
  :: forall y target.
     ( TensorKind y, ADReadyNoLet target, ShareTensor target
     , y ~ ADTensorKind y )
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalSame !s !c = \case
  -- All constructors that only admit a non-TKProduct kind
  -- (and the InputG constructor and the vector space constructors)
  -- can be handled here, where the extra
  -- constraint makes it easier.
  ScalarG d -> evalSame s (rmkRepScalar c) d
  UnScalarG d -> evalSame s (runRepScalar c) d
  InputG _ftk i ->
    let cs = repToM stensorKind c
    in s {iMap = DMap.adjust (addRepM cs) i
                 $ iMap s}
    -- This and similar don't need to be runtime-specialized,
    -- because the type of c determines the Num instance for (+).
    -- Note that we can't express sharing by inserting ShareG constructors
    -- into iMap, because often sharing needs to work across many
    -- iMap keys. That's why global sharing is used.
  -- By placing these here, we force their derivatives to be zeroed
  -- whenever they are called on non-base types, which they should not ever be.
  -- This is ensured by the types of the three constructors, assuming that
  -- no Num instances are defined for the non-base type tensors.
  ZeroG{} -> s
  ScaleG k d -> evalSame s (k * c) d
  AddG d e -> let cShared = tshare c
              in evalSame (evalSame s cShared d) cShared e

  IndexR d ix ->
    evalSame s (rscatter @target @_ @0
                         (shapeDelta d) c (const ix)) d
    -- equivalent: evalSame s (updateNR (treplicate0NR sh 0) [(ix, c)]) d
  SumR d ->
    evalSame s (rreplicate (lengthDelta d) c) d
  Sum0R d ->
    evalSame s (rreplicate0N (shapeDelta d) c) d
  Dot0R v vd ->
    evalSame s (v * rreplicate0N (rshape v) c) vd
      -- too slow: evalSame s (rmap0N (* (tscalar c)) v) vd
  ScatterR _sh d f ->
    evalSame s (rgather (shapeDelta d) c f) d
  FromVectorR @n1 @r ld ->
    let cShared = tshare c
        cxs :: [target (TKR r n1)]
        cxs = runravelToList cShared
    in foldl' (\ !s2 (cx, d2) -> evalSame s2 cx d2) s
       $ zip cxs (V.toList ld)
  ReplicateR _n d ->
    evalSame s (rsum c) d
  AppendR d e -> case rshape c of
    n :$: _ -> let cShared = tshare c
                   k = lengthDelta d
                   s2 = evalSame s (rslice 0 k cShared) d
               in evalSame s2 (rslice k (n - k) cShared) e
    ZSR -> error "evalSame: impossible pattern needlessly required"
  SliceR i n d -> case rshape c of
    n' :$: rest ->
      assert (n' == n `blame` (n', n)) $
      evalSame s (rconcat [ rzero (i :$: rest)
                          , c
                          , rzero (lengthDelta d - i - n :$: rest) ])
                  d
    ZSR -> error "evalSame: impossible pattern needlessly required"
  ReverseR d -> evalSame s (rreverse c) d
  TransposeR perm d ->
    let permR = permInverse perm
    in evalSame s (rtranspose permR c) d
  ReshapeR _sh d ->
    evalSame s (rreshape (shapeDelta d) c) d
  GatherR _sh d f ->
    evalSame s (rscatter (shapeDelta d) c f) d
  CastR @r1 @_ @n d ->
    evalRRuntimeSpecialized s (toADTensorKindShared (stensorKind @(TKR r1 n))
                               $ rcast c) d
  RFromS (SFromR d) -> evalSame s c d  -- no information lost, so no checks
  RFromS @sh d | Dict <- lemKnownNatRank (knownShS @sh) ->
    evalSame s (sfromR c) d
  RFromH d i ->
    let cs = V.map dynamicFromVoid $ shapeDeltaH d
        ci = DynamicRanked c
    in assert (dynamicsMatch (cs V.! i) ci) $
       evalSame s (dmkHVector $ cs V.// [(i, ci)]) d
        -- should be used only with small vectors or we end up with the same
        -- problem of summing a lot of one-hots as in indexing

  IndexS @sh1 @sh d ix ->
    gcastWith (unsafeCoerce Refl
               :: Drop (Rank sh1) (sh1 ++ sh) :~: sh) $
    gcastWith (unsafeCoerce Refl
               :: Take (Rank sh1) (sh1 ++ sh) :~: sh1) $
    withListSh (Proxy @sh1) $ \(_ :: IShR rankSh1) ->
    gcastWith (unsafeCoerce Refl :: rankSh1 :~: Rank sh1) $
    evalSame s (sscatter @_ @_ @'[] @(Rank sh1) c (const ix)) d
    -- equivalent: evalSame s (updateNR (replicate0NR sh 0) [(ix, c)]) d
  SumS d ->
    evalSame s (sreplicate c) d
  Sum0S d ->
    evalSame s (sreplicate0N c) d
  Dot0S v vd ->
    evalSame s (v * sreplicate0N c) vd
      -- too slow: evalSame s (smap0N (* (sscalar c)) v) vd
  ScatterS d f ->
    evalSame s (sgather c f) d
  FromVectorS ld ->
    let cShared = tshare c
    in V.ifoldl' (\ !s2 i d2 ->
         evalSame s2 (cShared !$ (fromIntegral i :.$ ZIS)) d2) s ld
  ReplicateS d ->
    evalSame s (ssum c) d
  AppendS @_ @_ @m d e ->
    let cShared = tshare c
        s2 = evalSame s (sslice (Proxy @0) Proxy cShared) d
    in evalSame s2 (sslice (Proxy @m) Proxy cShared) e
  SliceS @_ @i d ->
    evalSame s (sappend @_ @_ @i (srepl 0) (sappend c (srepl 0))) d
  ReverseS d -> evalSame s (sreverse c) d
  TransposeS @perm @sh2 perm d ->
    withShapeP (backpermutePrefixList (Permutation.permToList' perm)
                                      (shapeT @sh2)) $ \(Proxy @shp) ->
    gcastWith (unsafeCoerce Refl :: Permutation.PermutePrefix perm sh2 :~: shp) $
    Permutation.permInverse perm $ \(permRev :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerce Refl
                   :: Permutation.PermutePrefix permR (Permutation.PermutePrefix perm sh2) :~: sh2)
        $ gcastWith (unsafeCoerce Refl
                     :: Rank (Permutation.PermutePrefix perm sh2) :~: Rank sh2)
        $ gcastWith (unsafeCoerce Refl
                     :: Rank permR :~: Rank perm)
        $ evalSame s (stranspose permRev c) d
  ReshapeS d ->
    evalSame s (sreshape c) d
  GatherS d f ->
    evalSame s (sscatter c f) d
  CastS @r1 @_ @sh d ->
    evalSRuntimeSpecialized s (toADTensorKindShared (stensorKind @(TKS r1 sh))
                               $ scast c) d
  SFromR @sh (RFromS @sh2 d) ->
    case sameShape @sh @sh2 of
      Just Refl -> evalSame s c d
      _ -> error "evalSame: different shapes in SFromR(RFromS)"
  SFromR d ->
    evalSame s (rfromS c) d
  SFromH d i ->
    let cs = V.map dynamicFromVoid $ shapeDeltaH d
        ci = DynamicShaped c
    in assert (dynamicsMatch (cs V.! i) ci) $
       evalSame s (dmkHVector $ cs V.// [(i, ci)]) d

  IndexX{} -> error "TODO"
  FromVectorX @r @sh ld ->
    let cShared = tshare c
        f :: EvalState target -> Int -> Delta target (TKX r sh)
             -> EvalState target
        f !s2 i d2 = evalSame s2 (cShared `xindex` (fromIntegral i :.% ZIX)) d2
    in V.ifoldl' f s ld

  HToH v -> evalHVector s (tunvector c) v

  d -> evalR s c d
    -- the remaining constructors are already handled in evalR, so let's use that

evalDynamic
  :: (ADReadyNoLet target, ShareTensor target)
  => EvalState target
  -> (DynamicTensor target, DynamicTensor (Delta target))
  -> EvalState target
evalDynamic !s3 (t, DynamicRanked @r @n d2) =
  gcastWith (unsafeCoerce Refl :: TKR r n :~: ADTensorKind (TKR r n)) $
    -- this is a noble lie to maintain no ADTensorKind under HVector
    -- and at the same time re-use the new eval function also for HVector
  evalSame s3 (toADTensorKindShared (stensorKind @(TKR r n)) $ rfromD t) d2
evalDynamic s3 (t, DynamicShaped @r @sh d2) =
  gcastWith (unsafeCoerce Refl :: TKS r sh :~: ADTensorKind (TKS r sh)) $
  evalSame s3 (toADTensorKindShared (stensorKind @(TKS r sh)) $ sfromD t) d2
evalDynamic s3 (t, DynamicRankedDummy @r @sh _ _) =
  gcastWith (unsafeCoerce Refl :: TKR r (Rank sh) :~: ADTensorKind (TKR r (Rank sh))) $
  withListSh (Proxy @sh) $ \sh2 ->
    evalSame @(TKR r (Rank sh))
             s3 (toADTensorKindShared (stensorKind @(TKR r (Rank sh)))
                 $ rfromD @r t)
             (ZeroG $ FTKR sh2)
evalDynamic s3 (t, DynamicShapedDummy @r @sh _ _) =
  gcastWith (unsafeCoerce Refl :: TKS r sh :~: ADTensorKind (TKS r sh)) $
  evalSame @(TKS r sh)
        s3 (toADTensorKindShared (stensorKind @(TKS r sh)) $ sfromD t)
        (ZeroG $ FTKS knownShS)

evalHVector
  :: (ADReadyNoLet target, ShareTensor target)
  => EvalState target -> HVector target -> HVector (Delta target)
  -> EvalState target
evalHVector s as as' = V.foldl' evalDynamic s $ V.zip as as'

evalFromnMap :: forall target. (ADReadyNoLet target, ShareTensor target)
             => EvalState target -> EvalState target
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
            STKScalar _ -> case DMap.lookup n dMap of
              Just (RepAD c) -> evalR s2 c d
              Nothing -> errorMissing
            STKR @_ @n (STKScalar @r _) SNat -> case DMap.lookup n dMap of
              Just (RepAD c) -> evalRRuntimeSpecialized @n @r s2 c d
              Nothing -> errorMissing
            STKS @_ @sh (STKScalar @r _) sh -> withKnownShS sh $ case DMap.lookup n dMap  of
              Just (RepAD c) -> evalSRuntimeSpecialized @sh @r s2 c d
              Nothing -> errorMissing
            STKX (STKScalar _) sh -> withKnownShX sh $ case DMap.lookup n dMap of
              Just (RepAD c) -> evalR s2 c d
              Nothing -> errorMissing
            STKProduct{} -> case DMap.lookup n dMap of
              Just (RepAD c) -> evalR s2 c d
              Nothing -> errorMissing
            STKUntyped -> case DMap.lookup n dMap of
              Just (RepAD c) -> evalR s2 c d
              Nothing -> errorMissing
            _ -> error "TODO"
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
-- This mimics the reverse derivative code, but in reverse. Perhaps this can be
-- simplified, but the obvious simplest formulation does not honour sharing
-- and evaluates shared subexpressions repeatedly, so this state-passing
-- formulation is adopted.
fwdDynamic
  :: forall target. (ADReadyNoLet target, ShareTensor target)
  => IMap target -> ADMap target -> DynamicTensor (Delta target)
  -> (ADMap target, DynamicTensor target)
fwdDynamic params s (DynamicRanked @r @n d) =
  gcastWith (unsafeCoerce Refl :: TKR r n :~: ADTensorKind (TKR r n)) $
  second DynamicRanked $ fwdSame params s d
fwdDynamic params s (DynamicShaped @r @sh d) =
  gcastWith (unsafeCoerce Refl :: TKS r sh :~: ADTensorKind (TKS r sh)) $
  second DynamicShaped $ fwdSame params s d
fwdDynamic params s (DynamicRankedDummy @r @sh _ _) =
  gcastWith (unsafeCoerce Refl :: TKR r (Rank sh) :~: ADTensorKind (TKR r (Rank sh))) $
  withListSh (Proxy @sh) $ \sh2 ->
    second (DynamicRanked @r) $ fwdSame params s (ZeroG $ FTKR sh2)
fwdDynamic params s (DynamicShapedDummy @r @sh _ _) =
  gcastWith (unsafeCoerce Refl :: TKS r sh :~: ADTensorKind (TKS r sh)) $
  second (DynamicShaped @r @sh) $ fwdSame params s (ZeroG $ FTKS knownShS)

fwdHVector
  :: forall target. (ADReadyNoLet target, ShareTensor target)
  => IMap target -> ADMap target -> HVector (Delta target)
  -> (ADMap target,  HVector target)
fwdHVector params = mapAccumL (fwdDynamic params)

fwdR
  :: forall target y.
     (ADReadyNoLet target, ShareTensor target, TensorKind y)
  => IMap target -> ADMap target -> Delta target y
  -> (ADMap target, target (ADTensorKind y))
fwdR params s d0 = case d0 of
  PairG @y1 @y2 d1 d2 | Dict <- lemTensorKindOfAD (stensorKind @y1)
                      , Dict <- lemTensorKindOfAD (stensorKind @y2) ->
    let (s2, t) = fwdR params s d1
        (s3, u) = fwdR params s2 d2
    in (s3, tpair t u)
  Project1G @_ @z d | Dict <- lemTensorKindOfAD (stensorKind @y)
                    , Dict <- lemTensorKindOfAD (stensorKind @z) ->
    let (s2, v) = fwdR params s d
    in (s2, tproject1 v)
  Project2G @x d | Dict <- lemTensorKindOfAD (stensorKind @y)
                 , Dict <- lemTensorKindOfAD (stensorKind @x) ->
    let (s2, v) = fwdR params s d
    in (s2, tproject2 v)
  InputG _ftk inputId ->
    case DMap.lookup inputId params of
      Just dtk -> (s, toADTensorKindShared stensorKind $ evalRepM dtk)
      Nothing -> error "fwdR: missing input"
  ShareG n d | Dict <- lemTensorKindOfAD (stensorKind @y) ->
    case DMap.lookup n s of
      Just e1 -> (s, unRepAD e1)
      Nothing ->
        let (s2, cRaw) = fwdR params s d
            cShared = tshare cRaw
            cd = RepAD cShared
              -- cRaw is shared, because it's put into the map and then
              -- potentially looked up many times, so it'd get duplicated
            s3 = DMap.insert n cd s2
        in (s3, cShared)

  MapAccumR @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            df _rf acc0' es'
   | Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind accShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Just Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Just Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDTensorKind accShs
        bShsAD = aDTensorKind bShs
        eShsAD = aDTensorKind eShs
        (s2, cacc0) = fwdR params s acc0'
        (s3, ces) = fwdR params s2 es'
    in (s3, dmapAccumR (Proxy @target)
                       k accShsAD bShsAD (FTKProduct eShsAD
                                                     (FTKProduct accShs eShs))
                       (\dacc de_acc_e ->
                        tlet de_acc_e $ \ !de_acc_e1 ->
                          unHFun df (tpair (tpair dacc (tproject1 de_acc_e1))
                                           (tproject2 de_acc_e1)))
                       cacc0
                       (tpair ces (tpair q es)))
  MapAccumL @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            df _rf acc0' es'
   | Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind accShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Just Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Just Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDTensorKind accShs
        bShsAD = aDTensorKind bShs
        eShsAD = aDTensorKind eShs
        (s2, cacc0) = fwdR params s acc0'
        (s3, ces) = fwdR params s2 es'
    in (s3, dmapAccumL (Proxy @target)
                       k accShsAD bShsAD (FTKProduct eShsAD
                                                     (FTKProduct accShs eShs))
                       (\dacc de_acc_e ->
                        tlet de_acc_e $ \ !de_acc_e1 ->
                          unHFun df (tpair (tpair dacc (tproject1 de_acc_e1))
                                           (tproject2 de_acc_e1)))
                       cacc0
                       (tpair ces (tpair q es)))

  _ | Dict <- lemTensorKindOfAD (stensorKind @y) ->
      case sameTensorKind @y @(ADTensorKind y) of
        Just Refl -> fwdSame params s d0
        _ -> (s, repConstant 0 $ aDTensorKind $ shapeDeltaFull d0)

fwdSame
  :: forall target y.
     ( TensorKind y, ADReadyNoLet target, ShareTensor target
     , y ~ ADTensorKind y )
  => IMap target -> ADMap target -> Delta target y
  -> (ADMap target, target (ADTensorKind y))
fwdSame params s = \case
  ScalarG d -> let (s2, t) = fwdSame params s d
               in (s2, runRepScalar t)
  UnScalarG d -> let (s2, t) = fwdSame params s d
                 in (s2, rmkRepScalar t)
  InputG _ftk inputId ->
    case DMap.lookup inputId params of
      Just dtk -> (s, evalRepM dtk)
      Nothing -> error "fwdSame: missing input"
  -- See the comment about these three in evalSame.
  ZeroG ftk -> (s, repConstant0Old $ aDTensorKind ftk)  -- TODO: not repConstant only for backward compatibility with test results
  ScaleG k d -> second (* k) $ fwdSame params s d
  AddG d e -> let (s2, t) = fwdSame params s d
                  (s3, u) = fwdSame params s2 e
              in (s3, t + u)

  IndexR d ix -> second (`rindex` ix) $ fwdSame params s d
  SumR d -> second rsum $ fwdSame params s d
  Sum0R ZeroG{} -> (s, 0)
  Sum0R d -> second rsum0 $ fwdSame params s d
  Dot0R _ ZeroG{} -> (s, 0)
  Dot0R v d -> second (rdot0 v) $ fwdSame params s d
  ScatterR sh d f ->
    let (s2, t) = fwdSame params s d
    in (s2, rscatter sh t f)
  FromVectorR lsd ->
    let (s2, l) = mapAccumL (fwdSame params) s lsd
    in (s2, rfromVector l)
  ReplicateR n d ->
    let (s2, t) = fwdSame params s d
    in (s2, rreplicate n t)
  AppendR d e ->
    let (s2, t) = fwdSame params s d
        (s3, u) = fwdSame params s2 e
    in (s3, rappend t u)
  SliceR i n d -> second (rslice i n) $ fwdSame params s d
  ReverseR d -> second rreverse $ fwdSame params s d
  TransposeR perm d -> second (rtranspose perm) $ fwdSame params s d
  ReshapeR sh d -> second (rreshape sh) $ fwdSame params s d
  GatherR sh d f ->
    let (s2, t) = fwdSame params s d
    in (s2, rgather sh t f)
  d0@(CastR @r1 @_ @n d)
    | Dict <- lemTensorKindOfAD (stensorKind @(TKR r1 n)) ->
      case sameTensorKind @(TKR r1 n) @(ADTensorKind (TKR r1 n)) of
        Just Refl -> second rcast $ fwdSame params s d
        _ -> (s, repConstant 0 $ aDTensorKind $ shapeDeltaFull d0)
  RFromS (SFromR d) ->
    fwdSame params s d  -- no information lost, so no checks
  RFromS d -> second rfromS $ fwdSame params s d
  RFromH d i ->
    let (s2, v) = fwdSame params s d
    in (s2, rfromD $ dunHVector v V.! i)
-- Not needed, because we take only the i-th component of the vector,
-- so v is not copied.
--  in (s2, rfromD $ tunvector v) V.! i)

  IndexS d ix -> second (`sindex` ix) $ fwdSame params s d
  SumS d -> second ssum $ fwdSame params s d
  Sum0S ZeroG{} -> (s, srepl 0)
  Sum0S d -> second ssum0 $ fwdSame params s d
  Dot0S _ ZeroG{} -> (s, srepl 0)
  Dot0S v d -> second (sdot0 v) $ fwdSame params s d
  ScatterS d f ->
    let (s2, t) = fwdSame params s d
    in (s2, sscatter t f)
  FromVectorS lsd ->
    let (s2, l) = mapAccumL (fwdSame params) s lsd
    in (s2, sfromVector l)
  ReplicateS d ->
    let (s2, t) = fwdSame params s d
    in (s2, sreplicate t)
  AppendS d e ->
    let (s2, t) = fwdSame params s d
        (s3, u) = fwdSame params s2 e
    in (s3, sappend t u)
  SliceS @_ @i d -> second (sslice (Proxy @i) Proxy) $ fwdSame params s d
  ReverseS d -> second sreverse $ fwdSame params s d
  TransposeS perm d -> second (stranspose perm)
                       $ fwdSame params s d
  ReshapeS d -> second sreshape $ fwdSame params s d
  GatherS d f ->
    let (s2, t) = fwdSame params s d
    in (s2, sgather t f)
  d0@(CastS @r1 @_ @sh d)
    | Dict <- lemTensorKindOfAD (stensorKind @(TKS r1 sh)) ->
      case sameTensorKind @(TKS r1 sh) @(ADTensorKind (TKS r1 sh)) of
        Just Refl -> second scast $ fwdSame params s d
        _ -> (s, repConstant 0 $ aDTensorKind $ shapeDeltaFull d0)
  SFromR @sh (RFromS @sh2 d) ->
    case sameShape @sh @sh2 of
      Just Refl -> fwdSame params s d
      _ -> error "fwdSame: different shapes in SFromR(RFromS)"
  SFromR d -> second sfromR $ fwdSame params s d
  SFromH d i ->
    let (s2, v) = fwdSame params s d
    in (s2, sfromD $ dunHVector v V.! i)
-- Not needed, because we take only the i-th component of the vector,
-- so v is not copied.
--  in (s2, sfromD $ tunvector v V.! i)

  IndexX d ix -> second (`xindex` ix) $ fwdSame params s d
  FromVectorX lsd ->
    let (s2, l) = mapAccumL (fwdSame params) s lsd
    in (s2, xfromVector l)

  HToH v -> second dmkHVector
            $ fwdHVector params s v

  d -> fwdR params s d
