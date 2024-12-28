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
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Some
import Data.Strict.Vector qualified as Data.Vector
import Data.Traversable (mapAccumL)
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, sameNat, type (+), type (<=))
import Text.Show (showListWith)
import Text.Show.Functions ()
import Type.Reflection (typeRep)

import Data.Array.Mixed.Permutation (permInverse)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
  ( SMayNat (..)
  , pattern (:!%)
  , pattern (:.%)
  , pattern ZIX
  , pattern ZKX
  , shxAppend
  , shxDropSSX
  , shxTakeSSX
  )
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested
  ( IShR
  , KnownShS (..)
  , KnownShX (..)
  , MapJust
  , Rank
  , Replicate
  , ShR (..)
  , ShS (..)
  , ShX (..)
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape
  ( shCvtRX
  , shCvtSX
  , shCvtXR'
  , shrRank
  , shrTail
  , shsAppend
  , shsPermutePrefix
  , shsRank
  )
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

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
      s1 = evalR s0 dt deltaTopLevel
      s2 = evalFromnMap s1
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
        FTKUntyped shs ->
          let toDynamicTensor :: Some (RepM target)
                              -> DynamicTensor target
              toDynamicTensor (Some b) = case b of
                MTKScalar @r t -> DynamicRanked @r @0 $ rfromScalar t
                MTKR @y @n t | STKScalar @r _ <- stensorKind @y ->
                  DynamicRanked @r @n t
                MTKS @y @sh t | STKScalar @r _ <- stensorKind @y ->
                  DynamicShaped @r @sh t
                MTKScalarDummy @r -> DynamicRankedDummy @r @'[] Proxy Proxy
                MTKRDummy shr ftk | SNat <- shrRank shr
                                  , STKScalar @r _ <- ftkToStk ftk ->
                  withShapeP (toList shr) $ \(Proxy @sh) ->
                    DynamicRankedDummy @r @sh Proxy Proxy
                MTKSDummy @_ @sh sh ftk | STKScalar @r _ <- ftkToStk ftk ->
                  withKnownShS sh $
                  DynamicShapedDummy @r @sh Proxy Proxy
                _ -> error "rebuildInputs: unexpected type"
              len = V.length shs
              (els1, els2) = splitAt len els
          in ( dmkHVector
               $ V.fromList $ map toDynamicTensor els1
             , els2 )
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
        FTKUntyped{} ->
          let ts = tunvector t
              len = V.length ts
          in ( zipWith dynamicTensorToRepM [j ..] $ V.toList ts
             , j + len )
      iMap = DMap.fromDistinctAscList $ fst
             $ generateDSums 0 (tftk stensorKind ds) ds
      s0 = DMap.empty
      !(!_s2, !c) = fwdR iMap s0 deltaTopLevel
  in c

evalRepM :: forall target x. ADReadyNoLet target
         => RepM target x -> target x
evalRepM = \case
  MTKScalar t -> t
  MTKR t -> t
  MTKS t -> t
  MTKScalarDummy -> rtoScalar $ rscalar 0
  MTKRDummy shr ftk -> constantTarget 0 (FTKR shr ftk)
  MTKSDummy sh ftk -> constantTarget 0 (FTKS sh ftk)

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
  STKScalar{} -> MTKScalar t
  STKR SNat x | Dict <- lemTensorKindOfSTK x -> MTKR t
  STKS sh x | Dict <- lemTensorKindOfSTK x -> withKnownShS sh $ MTKS t
  STKX sh x | Dict <- lemTensorKindOfSTK x -> withKnownShX sh $ error "TODO"
  STKProduct{} -> error "repToM: unexpected type"
  STKUntyped{} -> error "repToM: unexpected type"

addRepM :: forall target y. ADReadyNoLet target
        => RepM target y -> RepM target y -> RepM target y
addRepM a b = case (a, b) of
  (MTKScalar ta, MTKScalar tb) ->
    MTKScalar $ rtoScalar $ rfromScalar ta + rfromScalar tb
  (MTKR ta, MTKR tb) | STKR _ STKScalar{} <- stensorKind @y -> MTKR $ ta + tb
  (MTKR ta, MTKR tb) -> MTKR $ addTarget stensorKind ta tb
  (MTKScalarDummy, _) -> b
  (_, MTKScalarDummy) -> a
  (MTKRDummy{}, _) -> b
  (_, MTKRDummy{}) -> a
  (MTKS ta, MTKS tb) | STKS _ STKScalar{} <- stensorKind @y -> MTKS $ ta + tb
  (MTKS ta, MTKS tb) -> MTKS $ addTarget stensorKind ta tb
  (MTKSDummy{}, _) -> b
  (_, MTKSDummy{}) -> a

-- This is very similar to DynamicTensor, but the second type parameter
-- gives a peek of what's inside, which is crucial for dependent maps
-- as opposed to existential vectors.
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
  Cast :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2)
       => Delta target (TKScalar r1) -> Delta target (TKScalar r2)
  FromScalarG :: GoodScalar r
              => Delta target (TKScalar r) -> Delta target (TKS '[] r)
  ToScalarG :: GoodScalar r
            => Delta target (TKS '[] r) -> Delta target (TKScalar r)
  PairG :: (TensorKind y, TensorKind z)
         => Delta target y -> Delta target z
         -> Delta target (TKProduct y z)
  Project1G :: forall x z target. (TensorKind x, TensorKind z)
            => Delta target (TKProduct x z) -> Delta target x
  Project2G :: forall x z target. (TensorKind x, TensorKind z)
            => Delta target (TKProduct x z) -> Delta target z
  InputG :: forall target y.
            FullTensorKind y -> InputId target y -> Delta target y
  ShareG :: NodeId target y -> Delta target y -> Delta target y
  ZeroG :: FullTensorKind y -> Delta target y
  ScaleG :: Num (target y)
         => target y -> Delta target y -> Delta target y
  AddG :: Num (target y)
       => Delta target y -> Delta target y -> Delta target y

  IndexR :: (TensorKind r, KnownNat n, KnownNat m)
         => Delta target (TKR2 (m + n) r) -> IxROf target m
         -> Delta target (TKR2 n r)
    -- ^ The sub-tensor at the given index. The given shape is of the
    -- large tensor. If index is out of bounds, the result is defined and is 0.
  SumR :: (TensorKind r, KnownNat n)
       => Delta target (TKR2 (1 + n) r) -> Delta target (TKR2 n r)
  Sum0R :: (TensorKind r, KnownNat n)
        => Delta target (TKR2 n r) -> Delta target (TKR2 0 r)
  Dot0R :: (KnownNat n, GoodScalar r)
        => target (TKR n r) -> Delta target (TKR n r) -> Delta target (TKR 0 r)
  ScatterR :: (TensorKind r, KnownNat m, KnownNat n, KnownNat p)
           => IShR (p + n) -> Delta target (TKR2 (m + n) r)
           -> (IxROf target m -> IxROf target p)
           -> Delta target (TKR2 (p + n) r)
    -- ^ Build a tensor by adding up tensors of rank @n@ taken from
    -- the third argument and inserted in a zero tensor
    -- at indexes of length @p@. Indexes of length 0 insert tensors trivially,
    -- so that, e.g, @Scatter1 5 (const ZR) (Replicate0R [5] d) []@ is equivalent
    -- to @5 * d@. If an index of length @p@ is out of bounds, no tensor
    -- is added at such an index (and similarly in @ScatterN@).
    -- The semantics of the operation permits index out of bounds
    -- and then no tensors is added at such an index.
    -- TODO: this is a haddock for Scatter1; fix.

  FromVectorR :: (KnownNat n, TensorKind r)
              => Data.Vector.Vector (Delta target (TKR2 n r))
              -> Delta target (TKR2 (1 + n) r)
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  ReplicateR :: (TensorKind r, KnownNat n)
             => Int -> Delta target (TKR2 n r)
             -> Delta target (TKR2 (1 + n) r)
    -- ^ Copy the given tensor along the new, outermost dimension.
  AppendR :: (TensorKind r, KnownNat n)
          => Delta target (TKR2 (1 + n) r)
          -> Delta target (TKR2 (1 + n) r)
          -> Delta target (TKR2 (1 + n) r)
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
  SliceR :: (TensorKind r, KnownNat n)
         => Int -> Int -> Delta target (TKR2 (1 + n) r)
         -> Delta target (TKR2 (1 + n) r)
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
  ReverseR :: (TensorKind r, KnownNat n)
           => Delta target (TKR2 (1 + n) r) -> Delta target (TKR2 (1 + n) r)
    -- ^ Reverse elements of the outermost dimension.
  TransposeR :: (TensorKind r, KnownNat n)
             => Permutation.PermR -> Delta target (TKR2 n r)
             -> Delta target (TKR2 n r)
    -- ^ Transpose according to the permutation.
  ReshapeR :: (TensorKind r, KnownNat n, KnownNat m)
           => IShR m -> Delta target (TKR2 n r)
           -> Delta target (TKR2 m r)
    -- ^ Change the shape of the tensor to the given one.
  GatherR :: (TensorKind r, KnownNat m, KnownNat n, KnownNat p)
          => IShR (m + n) -> Delta target (TKR2 (p + n) r)
          -> (IxROf target m -> IxROf target p)
          -> Delta target (TKR2 (m + n) r)
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @Gather1 (const ZR) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @GatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for Gather1; fix.
  CastR :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2, KnownNat n)
        => Delta target (TKR n r1) -> Delta target (TKR n r2)
  ZipR :: (TensorKind y, TensorKind z, KnownNat n)
       => Delta target (TKProduct (TKR2 n y) (TKR2 n z))
       -> Delta target (TKR2 n (TKProduct y z))
  UnzipR :: (TensorKind y, TensorKind z, KnownNat n)
         => Delta target (TKR2 n (TKProduct y z))
         -> Delta target (TKProduct (TKR2 n y) (TKR2 n z))
  RFromH :: (KnownNat n, GoodScalar r)
         => Delta target TKUntyped -> Int -> Delta target (TKR n r)

  IndexS :: ( TensorKind r, KnownShS shm, KnownShS shn
            , KnownShS (shm ++ shn) )  -- needed for the Show instance
         => Delta target (TKS2 (shm ++ shn) r)
         -> IxSOf target shm
         -> Delta target (TKS2 shn r)
    -- ^ The sub-tensor at the given index.
    -- If index is out of bounds, the result is defined and is 0.
  SumS :: (GoodScalar r, KnownNat n, KnownShS sh)
       => Delta target (TKS (n ': sh) r) -> Delta target (TKS sh r)
  Sum0S :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
        => Delta target (TKS sh r) -> Delta target (TKS '[] r)
  Dot0S :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
        => target (TKS sh r) -> Delta target (TKS sh r)
        -> Delta target (TKS '[] r)
  ScatterS :: forall target r shm shn shp.
              ( TensorKind r, KnownShS shm, KnownShS shn, KnownShS shp
              , KnownShS (shm ++ shn) )  -- needed for the Show instance
           => Delta target (TKS2 (shm ++ shn) r)
           -> (IxSOf target shm -> IxSOf target shp)
           -> Delta target (TKS2 (shp ++ shn) r)
    -- ^ Build a tensor by adding up tensors of rank @n@ taken from
    -- the third argument and inserted in a zero tensor
    -- at indexes of length @p@. Indexes of length 0 insert tensors trivially,
    -- so that, e.g, @Scatter1 5 (const ZR) (Replicate0R [5] d) []@ is equivalent
    -- to @5 * d@. If an index of length @p@ is out of bounds, no tensor
    -- is added at such an index (and similarly in @ScatterN@).
    -- The semantics of the operation permits index out of bounds
    -- and then no tensors is added at such an index.
    -- TODO: this is a haddock for Scatter1; fix.

  FromVectorS :: (TensorKind r, KnownShS sh, KnownNat n)
              => Data.Vector.Vector (Delta target (TKS2 sh r))
              -> Delta target (TKS2 (n ': sh) r)
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  ReplicateS :: forall target r n sh.
                (GoodScalar r, KnownShS sh, KnownNat n)
             => Delta target (TKS sh r) -> Delta target (TKS (n ': sh) r)
    -- ^ Copy the given tensor along the new, outermost dimension.
  AppendS :: forall target r m n sh.
             (TensorKind r, KnownNat m, KnownNat n, KnownShS sh)
          => Delta target (TKS2 (m ': sh) r)
          -> Delta target (TKS2 (n ': sh) r)
          -> Delta target (TKS2 ((m + n) ': sh) r)
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
    -- The integer argument is the outermost size of the first array.
  SliceS :: forall target i n k r sh.
            (TensorKind r, KnownNat i, KnownNat n, KnownNat k, KnownShS sh)
         => Delta target (TKS2 (i + n + k ': sh) r)
         -> Delta target (TKS2 (n ': sh) r)
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
    -- The last argument is the outermost size of the argument array.
  ReverseS :: (TensorKind r, KnownShS sh, KnownNat n)
           => Delta target (TKS2 (n ': sh) r)
           -> Delta target (TKS2 (n ': sh) r)
    -- ^ Reverse elements of the outermost dimension.
  TransposeS :: forall perm sh r target.
                (TensorKind r, PermC perm, KnownShS sh, Rank perm <= Rank sh)
             => Permutation.Perm perm
             -> Delta target (TKS2 sh r)
             -> Delta target (TKS2 (Permutation.PermutePrefix perm sh) r)
    -- ^ Transpose according to the permutation.
  ReshapeS :: ( TensorKind r, KnownShS sh, KnownShS sh2
              , Nested.Product sh
                ~ Nested.Product sh2 )
           => Delta target (TKS2 sh r)
           -> Delta target (TKS2 sh2 r)
    -- ^ Change the shape of the tensor from the first to the second.
  GatherS :: forall target r shm shn shp.
             ( TensorKind r, KnownShS shm, KnownShS shn, KnownShS shp
             , KnownShS (shp ++ shn) )  -- needed for the Show instance
          => Delta target (TKS2 (shp ++ shn) r)
          -> (IxSOf target shm -> IxSOf target shp)
          -> Delta target (TKS2 (shm ++ shn) r)
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @Gather1 (const ZR) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @GatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for Gather1; fix.
  CastS :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2, KnownShS sh)
        => Delta target (TKS sh r1) -> Delta target (TKS sh r2)
  ZipS :: (TensorKind y, TensorKind z, KnownShS sh)
       => Delta target (TKProduct (TKS2 sh y) (TKS2 sh z))
       -> Delta target (TKS2 sh (TKProduct y z))
  UnzipS :: (TensorKind y, TensorKind z, KnownShS sh)
         => Delta target (TKS2 sh (TKProduct y z))
         -> Delta target (TKProduct (TKS2 sh y) (TKS2 sh z))
  SFromH :: (KnownShS sh, GoodScalar r)
         => Delta target TKUntyped -> Int -> Delta target (TKS sh r)

  IndexX :: (KnownShX sh1, KnownShX sh2, KnownShX (sh1 ++ sh2), TensorKind r)
         => Delta target (TKX2 (sh1 ++ sh2) r)
         -> IxXOf target sh1
         -> Delta target (TKX2 sh2 r)
  FromVectorX :: (KnownNat n, KnownShX sh, TensorKind r)
              => Data.Vector.Vector (Delta target (TKX2 sh r))
              -> Delta target (TKX2 (Just n ': sh) r)
  ZipX :: (TensorKind y, TensorKind z, KnownShX sh)
       => Delta target (TKProduct (TKX2 sh y) (TKX2 sh z))
       -> Delta target (TKX2 sh (TKProduct y z))
  UnzipX :: (TensorKind y, TensorKind z, KnownShX sh)
         => Delta target (TKX2 sh (TKProduct y z))
         -> Delta target (TKProduct (TKX2 sh y) (TKX2 sh z))

  RFromS :: forall sh r target. (TensorKind r, KnownShS sh)
         => Delta target (TKS2 sh r)
         -> Delta target (TKR2 (Rank sh) r)
  RFromX :: forall sh r target. (TensorKind r, KnownShX sh)
         => Delta target (TKX2 sh r)
         -> Delta target (TKR2 (Rank sh) r)
  SFromR :: forall sh r target.
            (KnownShS sh, KnownNat (Rank sh), TensorKind r)
         => Delta target (TKR2 (Rank sh) r)
         -> Delta target (TKS2 sh r)
  SFromX :: forall sh sh' r target.
            (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', TensorKind r)
         => Delta target (TKX2 sh' r)
         -> Delta target (TKS2 sh r)
  XFromR :: (KnownShX sh, TensorKind r, KnownNat (Rank sh))
         => Delta target (TKR2 (Rank sh) r)
         -> Delta target (TKX2 sh r)
  XFromS :: (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', TensorKind r)
         => Delta target (TKS2 sh r)
         -> Delta target (TKX2 sh' r)

  -- The constraints about ++ in these three are needed for deriving Show.
  XNestR :: ( TensorKind x, KnownShX sh1, KnownNat m
            , KnownShX (sh1 ++ Replicate m Nothing) )
         => Delta target (TKX2 (sh1 ++ Replicate m Nothing) x)
         -> Delta target (TKX2 sh1 (TKR2 m x))
  XNestS :: ( TensorKind x, KnownShX sh1, KnownShS sh2
            , KnownShX (sh1 ++ MapJust sh2) )
         => Delta target (TKX2 (sh1 ++ MapJust sh2) x)
         -> Delta target (TKX2 sh1 (TKS2 sh2 x))
  XNest :: (TensorKind x, KnownShX sh1, KnownShX sh2, KnownShX (sh1 ++ sh2))
        => Delta target (TKX2 (sh1 ++ sh2) x)
        -> Delta target (TKX2 sh1 (TKX2 sh2 x))
  XUnNestR :: (TensorKind x, KnownShX sh1, KnownNat m)
           => Delta target (TKX2 sh1 (TKR2 m x))
           -> Delta target (TKX2 (sh1 ++ Replicate m Nothing) x)
  XUnNestS :: (TensorKind x, KnownShX sh1, KnownShS sh2)
           => Delta target (TKX2 sh1 (TKS2 sh2 x))
           -> Delta target (TKX2 (sh1 ++ MapJust sh2) x)
  XUnNest :: (TensorKind x, KnownShX sh1, KnownShX sh2)
          => Delta target (TKX2 sh1 (TKX2 sh2 x))
          -> Delta target (TKX2 (sh1 ++ sh2) x)

  HToH :: HVector (Delta target) -> Delta target TKUntyped
  MapAccumR
    :: forall target k accShs bShs eShs.
       ( TensorKind accShs, TensorKind bShs, TensorKind eShs
       , TensorKind (BuildTensorKind k eShs)
       , TensorKind (BuildTensorKind k accShs) )
    => SNat k
    -> FullTensorKind accShs
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
  MapAccumL
    :: forall target k accShs bShs eShs.
       ( TensorKind accShs, TensorKind bShs, TensorKind eShs
       , TensorKind (BuildTensorKind k eShs)
       , TensorKind (BuildTensorKind k accShs) )
    => SNat k
    -> FullTensorKind accShs
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

deriving instance ( TensorKind y
                  , Show (target TKUntyped)
                  , Show (IntOf target)
                  , (forall y7. TensorKind y7 => Show (target y7)) )
                  => Show (Delta target y)

shapeDeltaFull :: forall target y. TensorKind y
               => Delta target y -> FullTensorKind y
shapeDeltaFull = \case
  Cast{} -> FTKScalar
  FromScalarG{} -> FTKS ZSS FTKScalar
  ToScalarG{} -> FTKScalar
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

  IndexR d _ -> case shapeDeltaFull d of
    FTKR sh x -> FTKR (dropShape sh) x
  SumR d -> case shapeDeltaFull d of
    FTKR sh x -> FTKR (shrTail sh) x
  Sum0R d -> case shapeDeltaFull d of
    FTKR _ x -> FTKR ZSR x
  Dot0R{} -> FTKR ZSR FTKScalar
  ScatterR sh d _ -> case shapeDeltaFull d of
    FTKR _ x -> FTKR sh x
  FromVectorR l -> case V.toList l of
    [] -> case stensorKind @y of
      STKR @n SNat STKScalar{} -> case sameNat (Proxy @n) (Proxy @1) of
        Just Refl -> FTKR (0 :$: ZSR) FTKScalar
          -- the only case where we can guess the shape and x
        _ -> error "shapeDeltaFull: FromVectorR with no arguments"
      _ -> error "shapeDeltaFull: FromVectorR with no arguments"
    d : _ -> case shapeDeltaFull d of
      FTKR sh x -> FTKR (length l :$: sh) x
  ReplicateR n d -> case shapeDeltaFull d of
    FTKR sh x -> FTKR (n :$: sh) x
  AppendR a b -> case shapeDeltaFull a of
    FTKR ZSR _ -> error "shapeDeltaFull: impossible pattern needlessly required"
    FTKR (ai :$: ash) x -> case shapeDeltaFull b of
      FTKR ZSR _ -> error "shapeDeltaFull: impossible pattern needlessly required"
      FTKR (bi :$: _) _ -> FTKR (ai + bi :$: ash) x
  SliceR _ n d -> case shapeDeltaFull d of
    FTKR sh x -> FTKR (n :$: shrTail sh) x
  ReverseR d -> shapeDeltaFull d
  TransposeR perm d -> case shapeDeltaFull d of
    FTKR sh x -> FTKR (Nested.Internal.Shape.shrPermutePrefix perm sh) x
  ReshapeR sh d -> case shapeDeltaFull d of
    FTKR _ x -> FTKR sh x
  GatherR sh d _ -> case shapeDeltaFull d of
    FTKR _ x -> FTKR sh x
  CastR d -> FTKR (shapeDelta d) FTKScalar
  ZipR d -> case shapeDeltaFull d of
    FTKProduct (FTKR sh y) (FTKR _ z) -> FTKR sh (FTKProduct y z)
  UnzipR d -> case shapeDeltaFull d of
    FTKR sh (FTKProduct y z) -> FTKProduct (FTKR sh y) (FTKR sh z)
  RFromH d i -> FTKR (fromList $ shapeVoidDynamic (shapeDeltaH d V.! i)) FTKScalar

  IndexS d _ix -> case shapeDeltaFull d of
    FTKS _ x -> FTKS knownShS x
  SumS{} -> FTKS knownShS FTKScalar
  Sum0S{} -> FTKS knownShS FTKScalar
  Dot0S{} -> FTKS knownShS FTKScalar
  ScatterS @_ @_ @_ @shn @shp d _ -> case shapeDeltaFull d of
    FTKS _ x -> FTKS (knownShS @shp `shsAppend` knownShS @shn) x
  FromVectorS l -> case V.toList l of
    [] -> case stensorKind @y of
      STKS _ STKScalar{} -> FTKS knownShS FTKScalar
        -- the only case where we can guess the x
      _ -> error "shapeDeltaFull: FromVectorS with no arguments"
    d : _ -> case shapeDeltaFull d of
      FTKS _ x -> FTKS knownShS x
  ReplicateS{} -> FTKS knownShS FTKScalar
  AppendS a _ -> case shapeDeltaFull a of
    FTKS _ x -> FTKS knownShS x
  SliceS d -> case shapeDeltaFull d of
    FTKS _ x -> FTKS knownShS x
  ReverseS d -> shapeDeltaFull d
  TransposeS @_ @sh2 perm d -> case shapeDeltaFull d of
    FTKS _ x ->
      withKnownShS (shsPermutePrefix perm (knownShS @sh2)) $
      FTKS knownShS x
  ReshapeS d -> case shapeDeltaFull d of
    FTKS _ x -> FTKS knownShS x
  GatherS @_ @_ @shm @shn d _ -> case shapeDeltaFull d of
    FTKS _ x -> FTKS (knownShS @shm `shsAppend` knownShS @shn) x
  CastS{} -> FTKS knownShS FTKScalar
  ZipS d -> case shapeDeltaFull d of
    FTKProduct (FTKS sh y) (FTKS _ z) -> FTKS sh (FTKProduct y z)
  UnzipS d -> case shapeDeltaFull d of
    FTKS sh (FTKProduct y z) -> FTKProduct (FTKS sh y) (FTKS sh z)
  SFromH{} -> FTKS knownShS FTKScalar

  IndexX @sh1 d _ix -> case shapeDeltaFull d of
    FTKX sh x -> FTKX (shxDropSSX sh (knownShX @sh1)) x
  FromVectorX @n l -> case V.toList l of
    [] -> case stensorKind @y of
      STKX sh STKScalar{} -> case sh of
        (_ :!% ZKX) -> FTKX (SKnown (SNat @n) :$% ZSX) FTKScalar
        _ -> error "shapeDeltaFull: AstFromVectorX with no arguments"
      _ -> error "shapeDeltaFull: AstFromVectorX with no arguments"
    d : _ -> case shapeDeltaFull d of
      FTKX sh x -> FTKX (SKnown (SNat @n) :$% sh) x
  ZipX d -> case shapeDeltaFull d of
    FTKProduct (FTKX sh y) (FTKX _ z) -> FTKX sh (FTKProduct y z)
  UnzipX d -> case shapeDeltaFull d of
    FTKX sh (FTKProduct y z) -> FTKProduct (FTKX sh y) (FTKX sh z)

  RFromS @sh d
   | SNat <- shsRank (knownShS @sh) -> case shapeDeltaFull d of
    FTKS _ x -> FTKR (fromList $ toList $ knownShS @sh) x
  RFromX @sh d
   | SNat <- ssxRank (knownShX @sh) -> case shapeDeltaFull d of
    FTKX shx x -> FTKR (fromList $ toList shx) x
  SFromR d -> case shapeDeltaFull d of
    FTKR _ x -> FTKS knownShS x
  SFromX d -> case shapeDeltaFull d of
    FTKX _ x -> FTKS knownShS x
  XFromR @sh d
   | SNat <- ssxRank (knownShX @sh) -> case shapeDeltaFull d of
    FTKR shr x -> FTKX (fromList $ toList shr) x
  XFromS d -> case shapeDeltaFull d of
    FTKS sh x -> FTKX (fromList $ toList sh) x

  XNestR  @_ @sh1 @m d -> case shapeDeltaFull d of
    FTKX sh x -> FTKX (shxTakeSSX (Proxy @(Replicate m Nothing))
                                  sh (knownShX @sh1))
                      (FTKR (shCvtXR' (shxDropSSX sh (knownShX @sh1))) x)
  XNestS @_ @sh1 @sh2 d -> case shapeDeltaFull d of
    FTKX sh x -> FTKX (shxTakeSSX (Proxy @(MapJust sh2)) sh (knownShX @sh1))
                                  (FTKS knownShS x)
  XNest @_ @sh1 @sh2 d -> case shapeDeltaFull d of
    FTKX sh x -> FTKX (shxTakeSSX (Proxy @sh2) sh (knownShX @sh1))
                      (FTKX (shxDropSSX sh (knownShX @sh1)) x)
  XUnNestR d -> case shapeDeltaFull d of
    FTKX sh1 (FTKR sh2 x) -> FTKX (sh1 `shxAppend` shCvtRX sh2) x
  XUnNestS d -> case shapeDeltaFull d of
    FTKX sh1 (FTKS sh2 x) -> FTKX (sh1 `shxAppend` shCvtSX sh2) x
  XUnNest d -> case shapeDeltaFull d of
    FTKX sh1 (FTKX sh2 x) -> FTKX (sh1 `shxAppend` sh2) x

  HToH v ->
    FTKUntyped $ V.map (voidFromDynamicF (toList . shapeDelta)) v
  MapAccumR @_ @_ @_ @bShs k accShs bShs _eShs _q _es _df _rf _acc0' _es'
    | Dict <- lemTensorKindOfBuild k (stensorKind @bShs) ->
      FTKProduct accShs (buildFTK k bShs)
  MapAccumL @_ @_ @_ @bShs k accShs bShs _eShs _q _es _df _rf _acc0' _es'
    | Dict <- lemTensorKindOfBuild k (stensorKind @bShs) ->
      FTKProduct accShs (buildFTK k bShs)

shapeDelta :: forall target r n.
              (TensorKind r, KnownNat n)
           => Delta target (TKR2 n r) -> IShR n
shapeDelta t = case shapeDeltaFull t of
  FTKR sh _ -> sh

lengthDelta :: forall target r n.
               (TensorKind r, KnownNat n)
            => Delta target (TKR2 (1 + n) r) -> Int
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
        DynamicRankedDummy @r @sh _ _ | SNat @n <- shsRank (knownShS @sh) ->
          let shr :: IShR n
              shr = fromList (toList (knownShS @sh))
          in InputId n :=> MTKRDummy @(TKScalar r) shr FTKScalar
        DynamicShapedDummy @r @sh _ _ ->
          InputId n :=> MTKSDummy @(TKScalar r) @sh knownShS FTKScalar
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
evalRRuntimeSpecialized
  :: forall n r target.
     (GoodScalar r, KnownNat n, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind (TKR n r))
  -> Delta target (TKR n r)
  -> EvalState target
evalRRuntimeSpecialized !s !c =
  -- We dispatch on all expected underyling scalar types, which is
  -- necessary to run the correct specialization when unpacking
  -- an existential type. All IfDifferentiable and RowSum instances should
  -- be included in the list of expected underlying scalar types.
  -- If the scalar type is not on the list, performance suffers greatly.
  -- TODO: can I pattern match on (typeRep @r) instead?
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalSame @(TKR n Double) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalSame @(TKR n Float) s c
      _ -> const s

evalSRuntimeSpecialized
  :: forall sh r target.
     (GoodScalar r, KnownShS sh, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind (TKS sh r))
  -> Delta target (TKS sh r)
  -> EvalState target
evalSRuntimeSpecialized !s !c =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalSame @(TKS sh Double) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalSame @(TKS sh Float) s c
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
        let zero = constantTarget 0 $ aDFTK ftk2
        in evalR s (tpair c zero) d
    -- if y is, e.g., TKR Int 0, we eval this delta even though we could ignore it
    -- at the price of complicating or duplicating the code slightly more
  Project2G @x d | Dict <- lemTensorKindOfAD (stensorKind @y)
                 , Dict <- lemTensorKindOfAD (stensorKind @x) ->
    case shapeDeltaFull d of
      FTKProduct ftk1 _ ->
        let zero = constantTarget 0 $ aDFTK ftk1
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
    assert (case d of  -- shouold match shareDelta
              ZeroG{} -> False
              PairG{} -> False
              HToH{} -> False
              InputG{} -> False
              ShareG{} -> False
              _ -> True)
    $ case DMap.lookup n $ nMap s of
        Just _ ->
          let addc x = RepAD $ addTarget stensorKind c (unRepAD x)
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
        s2 = evalR s dacc acc0'
    in evalR s2 des es'
  MapAccumL @_ @_ @accShs @bShs @eShs
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
  Cast @r1 d ->
    evalR s (toADTensorKindShared (stensorKind @(TKScalar r1))
             $ kcast c) d
  FromScalarG d -> evalSame s (stoScalar c) d
  ToScalarG d -> evalSame s (sfromScalar c) d
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

  IndexR d ix -> evalSame s (roneHot (takeShape $ shapeDelta d) c ix) d
  SumR d ->
    evalSame s (rreplicate (lengthDelta d) c) d
  Sum0R d ->
    evalSame s (rreplicate0N (shapeDelta d) c) d
  Dot0R v vd ->
    evalSame s (v * rreplicate0N (rshape v) c) vd
      -- too slow: evalSame s (rmap0N (* (tscalar c)) v) vd
  ScatterR _sh d f ->
    evalSame s (rgather (shapeDelta d) c f) d
  FromVectorR ld ->
    let cShared = tshare c
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
  SliceR i n d -> case tftk (stensorKind @y) c of
    FTKR (n' :$: rest) x ->
      assert (n' == n `blame` (n', n)) $
      evalSame s
               (rconcat
                  [ constantTarget 0 (FTKR (i :$: rest) x)
                  , c
                  , constantTarget 0 (FTKR (lengthDelta d - i - n :$: rest) x) ])
               d
    FTKR ZSR _ -> error "evalSame: impossible pattern needlessly required"
  ReverseR d -> evalSame s (rreverse c) d
  TransposeR perm d ->
    let permR = permRInverse perm
    in evalSame s (rtranspose permR c) d
  ReshapeR _sh d ->
    evalSame s (rreshape (shapeDelta d) c) d
  GatherR _sh d f ->
    evalSame s (rscatter (shapeDelta d) c f) d
  CastR @r1 @_ @n d ->
    evalRRuntimeSpecialized s (toADTensorKindShared (stensorKind @(TKR n r1))
                               $ rcast c) d
  ZipR d ->
    evalSame s (runzip c) d
  UnzipR d ->
    evalSame s (rzip c) d
  RFromH d i ->
    let cs = V.map dynamicFromVoid $ shapeDeltaH d
        ci = DynamicRanked c
    in assert (dynamicsMatch (cs V.! i) ci) $
       evalSame s (dmkHVector $ cs V.// [(i, ci)]) d
        -- should be used only with small vectors or we end up with the same
        -- problem of summing a lot of one-hots as in indexing

  IndexS d ix -> evalSame s (soneHot c ix) d
  SumS d ->
    evalSame s (sreplicate c) d
  Sum0S d ->
    evalSame s (sreplicate0N c) d
  Dot0S v vd ->
    evalSame s (v * sreplicate0N c) vd
      -- too slow: evalSame s (smap0N (* (sscalar c)) v) vd
  ScatterS @_ @_ @shm @shn @shp d f ->
    evalSame s (sgather @_ @_ @shm @shn @shp c f) d
  FromVectorS ld ->
    let cShared = tshare c
        cxs = sunravelToList cShared
    in foldl' (\ !s2 (cx, d2) -> evalSame s2 cx d2) s
       $ zip cxs (V.toList ld)
  ReplicateS d ->
    evalSame s (ssum c) d
  AppendS @_ @_ @m d e ->
    let cShared = tshare c
        s2 = evalSame s (sslice (Proxy @0) Proxy cShared) d
    in evalSame s2 (sslice (Proxy @m) Proxy cShared) e
  SliceS @_ @i d -> case tftk (stensorKind @y) c of
    FTKS _ x -> evalSame s (sappend @_ @_ @i
                              (constantTarget 0 (FTKS knownShS x))
                              (sappend
                                 c (constantTarget 0 (FTKS knownShS x)))) d
  ReverseS d -> evalSame s (sreverse c) d
  TransposeS @perm @sh2 perm d ->
    withKnownShS (shsPermutePrefix perm (knownShS @sh2)) $
    permInverse perm $ \(permRev :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permR (Permutation.PermutePrefix perm sh2) :~: sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank (Permutation.PermutePrefix perm sh2) :~: Rank sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank permR :~: Rank perm)
        $ evalSame s (stranspose permRev c) d
  ReshapeS d ->
    evalSame s (sreshape c) d
  GatherS @_ @_ @shm @shn @shp d f ->
    evalSame s (sscatter @_ @_ @shm @shn @shp c f) d
  CastS @r1 @_ @sh d ->
    evalSRuntimeSpecialized s (toADTensorKindShared (stensorKind @(TKS sh r1))
                               $ scast c) d
  ZipS d ->
    evalSame s (sunzip c) d
  UnzipS d ->
    evalSame s (szip c) d
  SFromH d i ->
    let cs = V.map dynamicFromVoid $ shapeDeltaH d
        ci = DynamicShaped c
    in assert (dynamicsMatch (cs V.! i) ci) $
       evalSame s (dmkHVector $ cs V.// [(i, ci)]) d

  IndexX{} -> error "TODO"
  FromVectorX @_ @sh @r ld ->
    let cShared = tshare c
        f :: EvalState target -> Int -> Delta target (TKX2 sh r)
             -> EvalState target
        f !s2 i d2 = evalSame s2 (cShared `xindex` (fromIntegral i :.% ZIX)) d2
    in V.ifoldl' f s ld
  ZipX d ->
    evalSame s (xunzip c) d
  UnzipX d ->
    evalSame s (xzip c) d

  RFromS (SFromR d) -> evalSame s c d  -- no information lost, so no checks
  RFromS @sh d | SNat <- shsRank (knownShS @sh) ->
    evalSame s (sfromR c) d
  RFromX @sh d | SNat <- ssxRank (knownShX @sh) ->
    evalSame s (xfromR c) d
  SFromR @sh (RFromS @sh2 d) ->
    case sameShape @sh @sh2 of
      Just Refl -> evalSame s c d
      _ -> error "evalSame: different shapes in SFromR(RFromS)"
  SFromR d ->
    evalSame s (rfromS c) d
  SFromX @sh (XFromS @sh2 d) ->
    case sameShape @sh @sh2 of
      Just Refl -> evalSame s c d
      _ -> error "evalSame: different shapes in SFromX(XFromS)"
  SFromX d ->
    evalSame s (xfromS c) d
-- impossible, shapes may differ: XFromS (SFromX d) -> evalSame s c d
  XFromR @sh d | SNat <- ssxRank (knownShX @sh) ->
    evalSame s (rfromX c) d
  XFromS d ->
    evalSame s (sfromX c) d

  XNestR d ->
    evalSame s (xunNestR c) d
  XNestS d ->
    evalSame s (xunNestS c) d
  XNest d ->
    evalSame s (xunNest c) d
  XUnNestR d ->
    evalSame s (xnestR knownShX c) d
  XUnNestS d ->
    evalSame s (xnestS knownShX c) d
  XUnNest d ->
    evalSame s (xnest knownShX c) d

  HToH v -> evalHVector s (tunvector c) v

  d -> evalR s c d
    -- the remaining constructors are already handled in evalR, so let's use that

evalDynamic
  :: (ADReadyNoLet target, ShareTensor target)
  => EvalState target
  -> (DynamicTensor target, DynamicTensor (Delta target))
  -> EvalState target
evalDynamic !s3 (t, DynamicRanked @r @n d2) =
  gcastWith (unsafeCoerceRefl :: TKR n r :~: ADTensorKind (TKR n r)) $
    -- this is a noble lie to maintain no ADTensorKind under HVector
    -- and at the same time re-use the new eval function also for HVector
  evalSame s3 (toADTensorKindShared (stensorKind @(TKR n r)) $ rfromD t) d2
evalDynamic s3 (t, DynamicShaped @r @sh d2) =
  gcastWith (unsafeCoerceRefl :: TKS sh r :~: ADTensorKind (TKS sh r)) $
  evalSame s3 (toADTensorKindShared (stensorKind @(TKS sh r)) $ sfromD t) d2
evalDynamic s3 (t, DynamicRankedDummy @r @sh _ _) =
  gcastWith (unsafeCoerceRefl :: TKR (Rank sh) r :~: ADTensorKind (TKR (Rank sh) r)) $
  withListSh (Proxy @sh) $ \sh2 ->
    evalSame @(TKR (Rank sh) r)
             s3 (toADTensorKindShared (stensorKind @(TKR (Rank sh) r))
                 $ rfromD @r t)
             (ZeroG $ FTKR sh2 FTKScalar)
evalDynamic s3 (t, DynamicShapedDummy @r @sh _ _) =
  gcastWith (unsafeCoerceRefl :: TKS sh r :~: ADTensorKind (TKS sh r)) $
  evalSame @(TKS sh r)
        s3 (toADTensorKindShared (stensorKind @(TKS sh r)) $ sfromD t)
        (ZeroG $ FTKS knownShS FTKScalar)

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
            STKR @n SNat (STKScalar @r _) -> case DMap.lookup n dMap of
              Just (RepAD c) -> evalRRuntimeSpecialized @n @r s2 c d
              Nothing -> errorMissing
            STKS @sh sh (STKScalar @r _) ->
              withKnownShS sh $ case DMap.lookup n dMap of
                Just (RepAD c) -> evalSRuntimeSpecialized @sh @r s2 c d
                Nothing -> errorMissing
            _ -> case DMap.lookup n dMap of
              Just (RepAD c) -> evalR s2 c d
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
-- This mimics the reverse derivative code, but in reverse. Perhaps this can be
-- simplified, but the obvious simplest formulation does not honour sharing
-- and evaluates shared subexpressions repeatedly, so this state-passing
-- formulation is adopted.
fwdDynamic
  :: forall target. (ADReadyNoLet target, ShareTensor target)
  => IMap target -> ADMap target -> DynamicTensor (Delta target)
  -> (ADMap target, DynamicTensor target)
fwdDynamic params s (DynamicRanked @r @n d) =
  gcastWith (unsafeCoerceRefl :: TKR n r :~: ADTensorKind (TKR n r)) $
  second DynamicRanked $ fwdSame params s d
fwdDynamic params s (DynamicShaped @r @sh d) =
  gcastWith (unsafeCoerceRefl :: TKS sh r :~: ADTensorKind (TKS sh r)) $
  second DynamicShaped $ fwdSame params s d
fwdDynamic params s (DynamicRankedDummy @r @sh _ _) =
  gcastWith (unsafeCoerceRefl :: TKR (Rank sh) r :~: ADTensorKind (TKR (Rank sh) r)) $
  withListSh (Proxy @sh) $ \sh2 ->
    second (DynamicRanked @r) $ fwdSame params s (ZeroG $ FTKR sh2 FTKScalar)
fwdDynamic params s (DynamicShapedDummy @r @sh _ _) =
  gcastWith (unsafeCoerceRefl :: TKS sh r :~: ADTensorKind (TKS sh r)) $
  second (DynamicShaped @r @sh) $ fwdSame params s (ZeroG $ FTKS knownShS FTKScalar)

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
   , Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind accShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDFTK accShs
        bShsAD = aDFTK bShs
        eShsAD = aDFTK eShs
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
   , Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind accShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDFTK accShs
        bShsAD = aDFTK bShs
        eShsAD = aDFTK eShs
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
        _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)

fwdSame
  :: forall target y.
     ( TensorKind y, ADReadyNoLet target, ShareTensor target
     , y ~ ADTensorKind y )
  => IMap target -> ADMap target -> Delta target y
  -> (ADMap target, target (ADTensorKind y))
fwdSame params s = \case
  d0@(Cast @r1 d)
    | Dict <- lemTensorKindOfAD (stensorKind @(TKScalar r1)) ->
      case sameTensorKind @(TKScalar r1) @(ADTensorKind (TKScalar r1)) of
        Just Refl -> second kcast $ fwdSame params s d
        _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)
  FromScalarG d -> let (s2, t) = fwdSame params s d
                   in (s2, sfromScalar t)
  ToScalarG d -> let (s2, t) = fwdSame params s d
                 in (s2, stoScalar t)
  InputG _ftk inputId ->
    case DMap.lookup inputId params of
      Just dtk -> (s, evalRepM dtk)
      Nothing -> error "fwdSame: missing input"
  -- See the comment about these three in evalSame.
  ZeroG ftk -> (s, constantTarget 0 $ aDFTK ftk)
  ScaleG k d -> second (* k) $ fwdSame params s d
  AddG d e -> let (s2, t) = fwdSame params s d
                  (s3, u) = fwdSame params s2 e
              in (s3, t + u)

  IndexR d ix -> second (`rindex` ix) $ fwdSame params s d
  SumR d -> second rsum $ fwdSame params s d
  Sum0R (ZeroG (FTKR _ x)) -> (s, constantTarget 0 (FTKR ZSR x))
  Sum0R d -> second rsum0 $ fwdSame params s d
  Dot0R _ ZeroG{} -> (s, rscalar 0)
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
    | Dict <- lemTensorKindOfAD (stensorKind @(TKR n r1)) ->
      case sameTensorKind @(TKR n r1) @(ADTensorKind (TKR n r1)) of
        Just Refl -> second rcast $ fwdSame params s d
        _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)
  ZipR d -> second rzip $ fwdSame params s d
  UnzipR d -> second runzip $ fwdSame params s d
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
  ScatterS @_ @_ @shm @shn @shp d f ->
    let (s2, t) = fwdSame params s d
    in (s2, sscatter @_ @_ @shm @shn @shp t f)
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
  GatherS @_ @_ @shm @shn @shp d f ->
    let (s2, t) = fwdSame params s d
    in (s2, sgather @_ @_ @shm @shn @shp t f)
  d0@(CastS @r1 @_ @sh d)
    | Dict <- lemTensorKindOfAD (stensorKind @(TKS sh r1)) ->
      case sameTensorKind @(TKS sh r1) @(ADTensorKind (TKS sh r1)) of
        Just Refl -> second scast $ fwdSame params s d
        _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)
  ZipS d -> second szip $ fwdSame params s d
  UnzipS d -> second sunzip $ fwdSame params s d
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
  ZipX d -> second xzip $ fwdSame params s d
  UnzipX d -> second xunzip $ fwdSame params s d

  RFromS (SFromR d) ->
    fwdSame params s d  -- no information lost, so no checks
  RFromS d -> second rfromS $ fwdSame params s d
  RFromX d -> second rfromX $ fwdSame params s d
  SFromR @sh (RFromS @sh2 d) ->
    case sameShape @sh @sh2 of
      Just Refl -> fwdSame params s d
      _ -> error "fwdSame: different shapes in SFromR(RFromS)"
  SFromR d -> second sfromR $ fwdSame params s d
  XFromR @sh d | SNat <- ssxRank (knownShX @sh) ->
    second xfromR $ fwdSame params s d
  XFromS d -> second xfromS $ fwdSame params s d
  SFromX @sh (XFromS @sh2 d) ->
    case sameShape @sh @sh2 of
      Just Refl -> fwdSame params s d
      _ -> error "fwdSame: different shapes in SFromX(XFromS)"
  SFromX d -> second sfromX $ fwdSame params s d

  XNestR d -> second (xnestR knownShX) $ fwdSame params s d
  XNestS d -> second (xnestS knownShX) $ fwdSame params s d
  XNest d -> second (xnest knownShX) $ fwdSame params s d
  XUnNestR d -> second xunNestR $ fwdSame params s d
  XUnNestS d -> second xunNestS $ fwdSame params s d
  XUnNest d -> second xunNest $ fwdSame params s d

  HToH v -> second dmkHVector
            $ fwdHVector params s v

  d -> fwdR params s d
